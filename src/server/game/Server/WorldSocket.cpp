/*
* This file is part of the Pandaria 5.4.8 Project. See THANKS file for Copyright information
*
* This program is free software; you can redistribute it and/or modify it
* under the terms of the GNU General Public License as published by the
* Free Software Foundation; either version 2 of the License, or (at your
* option) any later version.
*
* This program is distributed in the hope that it will be useful, but WITHOUT
* ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
* FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for
* more details.
*
* You should have received a copy of the GNU General Public License along
* with this program. If not, see <http://www.gnu.org/licenses/>.
*/

#include "WorldSocket.h"
#include "BigNumber.h"
#include "DatabaseEnv.h"
#include "GameTime.h"
#include "CryptoHash.h"
#include "CryptoRandom.h"
#include "IPLocation.h"
#include "Opcodes.h"
#include "PacketLog.h"
#include "Random.h"
//#include "RBAC.h"
#include "Realm.h"
#include "ScriptMgr.h"
#include "World.h"
#include "WorldSession.h"
#include <memory>
#include <zlib.h>
//#include "ServerPktHeader.h"

#pragma pack(push, 1)

struct CompressedWorldPacket
{
    uint32 UncompressedSize;
    uint32 UncompressedAdler;
    uint32 CompressedAdler;
};

#pragma pack(pop)

std::string const WorldSocket::ServerConnectionInitialize("WORLD OF WARCRAFT CONNECTION - SERVER TO CLIENT");
std::string const WorldSocket::ClientConnectionInitialize("WORLD OF WARCRAFT CONNECTION - CLIENT TO SERVER");
uint32 const WorldSocket::MinSizeForCompression = 0x400;

uint32 const SizeOfClientHeader = sizeof(uint32) + sizeof(uint16);
uint32 const SizeOfServerHeader = sizeof(uint32) + sizeof(uint16);


struct ServerPktHeader
{
    ServerPktHeader(uint32 size, uint32 cmd, bool encrypt, AuthCrypt* _authCrypt) : size(size)
    {
        if (encrypt && _authCrypt->IsInitialized())
        {
            uint32 data = (size << 13) | (cmd & MAX_OPCODE);
            memcpy(&header[0], &data, 4);
            _authCrypt->EncryptSend((uint8*)&header[0], getHeaderLength());
        }
        else
        {
            // Dynamic header size is not needed anymore, we are using not encrypted part for only the first few packets
            memcpy(&header[0], &size, 2);
            memcpy(&header[2], &cmd, 2);
        }
    }

    uint8 getHeaderLength()
    {
        return 4;
    }

    const uint32 size;
    uint8 header[4];
};

using boost::asio::ip::tcp;

WorldSocket::WorldSocket(tcp::socket&& socket)
    : Socket(std::move(socket)), _OverSpeedPings(0), _worldSession(nullptr), _authed(false), _sendBufferSize(4096), _compressionStream(nullptr)
{
    Trinity::Crypto::GetRandomBytes(_authSeed);
    _headerBuffer.Resize(2);
}

WorldSocket::~WorldSocket()
{
    if (_compressionStream)
    {
        deflateEnd(_compressionStream);
        delete _compressionStream;
    }

}

void WorldSocket::Start()
{
    std::string ip_address = GetRemoteIpAddress().to_string();
    LoginDatabasePreparedStatement* stmt = LoginDatabase.GetPreparedStatement(LOGIN_SEL_IP_INFO);
    stmt->setString(0, ip_address);

    _queryProcessor.AddCallback(LoginDatabase.AsyncQuery(stmt).WithPreparedCallback(std::bind(&WorldSocket::CheckIpCallback, this, std::placeholders::_1)));
}

void WorldSocket::CheckIpCallback(PreparedQueryResult result)
{
    if (result)
    {
        bool banned = false;
        do
        {
            Field* fields = result->Fetch();
            if (fields[0].GetUInt64() != 0)
                banned = true;

        } while (result->NextRow());

        if (banned)
        {
            SendAuthResponseError(AUTH_REJECT);
            TC_LOG_ERROR("network", "WorldSocket::CheckIpCallback: Sent Auth Response (IP %s banned).", GetRemoteIpAddress().to_string().c_str());
            DelayedCloseSocket();
            return;
        }
    }

    AsyncRead();

    MessageBuffer initializer;
    ServerPktHeader header(ServerConnectionInitialize.size(), 0, false, &_authCrypt);
    initializer.Write(header.header, header.getHeaderLength() - 2);
    initializer.Write(ServerConnectionInitialize.c_str(), ServerConnectionInitialize.length());

    // - io_service.run thread, safe.
    QueuePacket(std::move(initializer));

}

bool WorldSocket::Update()
{
    EncryptablePacket* queued;
    MessageBuffer buffer(_sendBufferSize);
    while (_bufferQueue.Dequeue(queued))
    {
        // if (queued->size() > 0x400 && !queued->IsCompressed())
        //     queued->Compress(_compressionStream);
        //ServerPktHeader header(queued->size() + 2, queued->GetOpcode(), &_authCrypt);
        //ServerPktHeader header(!_authCrypt.IsInitialized() ? queued->size() + 2 : queued->size(), queued->GetOpcode(), &_authCrypt);
        //ServerPktHeader header(!_authCrypt.IsInitialized() ? queued->size() + 2 : queued->size(), queued->GetOpcode(), queued->NeedsEncryption(), &_authCrypt);
        ServerPktHeader header(!_authCrypt.IsInitialized() ? queued->size() + 2 : queued->size(), queued->GetOpcode(), queued->NeedsEncryption(), &_authCrypt);
        //ServerPktHeader header(!_authCrypt.IsInitialized() ? queued->size() + 2 : queued->size(), queued->GetOpcode(), false, &_authCrypt);
        // if (queued->NeedsEncryption())
        //     _authCrypt.EncryptSend(header.header, header.getHeaderLength());

        if (buffer.GetRemainingSpace() < queued->size() + header.getHeaderLength())
        {
            QueuePacket(std::move(buffer));
            buffer.Resize(_sendBufferSize);
        }

        if (buffer.GetRemainingSpace() >= queued->size() + header.getHeaderLength())
        {
            buffer.Write(header.header, header.getHeaderLength());
            if (!queued->empty())
                buffer.Write(queued->contents(), queued->size());
        }
        else    // single packet larger than 4096 bytes
        {
            MessageBuffer packetBuffer(queued->size() + header.getHeaderLength());
            packetBuffer.Write(header.header, header.getHeaderLength());
            if (!queued->empty())
                packetBuffer.Write(queued->contents(), queued->size());

            QueuePacket(std::move(packetBuffer));
        }

        delete queued;
    }

    if (buffer.GetActiveSize() > 0)
        QueuePacket(std::move(buffer));

    if (!BaseSocket::Update())
        return false;

    _queryProcessor.ProcessReadyCallbacks();

    return true;
}

void WorldSocket::HandleSendAuthSession()
{
    WorldPacket packet(SMSG_AUTH_CHALLENGE, 37);
    packet << uint16(0); // header?

    packet.append(Trinity::Crypto::GetRandomBytes<32>());               // new encryption seeds
    packet << uint8(1);
    packet.append(_authSeed);

    SendPacketAndLogOpcode(packet);
}

void WorldSocket::OnClose()
{
    {
        std::lock_guard<std::mutex> sessionGuard(_worldSessionLock);
        _worldSession = nullptr;
    }
}

void WorldSocket::ReadHandler()
{
    if (!IsOpen())
        return;

    MessageBuffer& packet = GetReadBuffer();
    while (packet.GetActiveSize() > 0)
    {
        
        if (_headerBuffer.GetRemainingSpace() > 0)
        {
            // need to receive the header
            std::size_t readHeaderSize = std::min(packet.GetActiveSize(), _headerBuffer.GetRemainingSpace());
            _headerBuffer.Write(packet.GetReadPointer(), readHeaderSize);
            packet.ReadCompleted(readHeaderSize);

            if (_headerBuffer.GetRemainingSpace() > 0)
            {
                // Couldn't receive the whole header this time.
                ASSERT(packet.GetActiveSize() == 0);
                break;
            }

            // We just received nice new header
            if (!ReadHeaderHandler())
            {
                CloseSocket();
                return;
            }
        }

        // We have full read header, now check the data payload
        if (_packetBuffer.GetRemainingSpace() > 0)
        {
            // need more data in the payload
            std::size_t readDataSize = std::min(packet.GetActiveSize(), _packetBuffer.GetRemainingSpace());
            _packetBuffer.Write(packet.GetReadPointer(), readDataSize);
            packet.ReadCompleted(readDataSize);

            if (_packetBuffer.GetRemainingSpace() > 0)
            {
                // Couldn't receive the whole data this time.
                ASSERT(packet.GetActiveSize() == 0);
                break;
            }
        }

        // just received fresh new payload
        ReadDataHandlerResult result = ReadDataHandler();
        _headerBuffer.Reset();
        if (result != ReadDataHandlerResult::Ok)
        {
            if (result != ReadDataHandlerResult::WaitingForQuery)
            {
                CloseSocket();
            }

            return;
        }
    }

    AsyncRead();
}

bool WorldSocket::ReadHeaderHandler()
{

    if (_authCrypt.IsInitialized())
    {
        
        uint8* uintHeader = (uint8*)_headerBuffer.GetReadPointer();
        _authCrypt.DecryptRecv(uintHeader, sizeof(WorldClientPktHeader)); 
        WorldClientPktHeader* header = reinterpret_cast<WorldClientPktHeader*>(_headerBuffer.GetReadPointer());

        uint32 value = *(uint32*)uintHeader;
        header->cmd = value & 0x1FFF;
        header->size = ((value & ~(uint32)0x1FFF) >> 13);

        // if (header->size > 10236)
        // {
        //     Player* _player = _worldSession ? _worldSession->GetPlayer() : nullptr; // Removed this because it crashes the server if the player disconnects right before the log
        //     return false;
        // }
        //OpcodeClient opcode = static_cast<OpcodeClient>(PacketFilter::DropHighBytes(header->cmd));
        _packetBuffer.Resize(header->size);

    }
    else
    {

        ClientPktHeader* header = reinterpret_cast<ClientPktHeader*>(_headerBuffer.GetReadPointer());
        // EndianConvertReverse(header->size);
        // EndianConvert(header->cmd);       
        
        // if ((header->size < 4) || (header->size > 10240))
        // {
        //     Player* _player = _worldSession ? _worldSession->GetPlayer() : nullptr; // Removed this because it crashes the server if the player disconnects right before the log
        //     return false;
        // }

        if (_initialized)
            header->size -= sizeof(header->cmd);

        if (header->IsValidSize() && header->IsValidOpcode()) // header->size > 0
        {
            _packetBuffer.Resize(header->size);
        }
    }

    return true;
}

struct AuthSession
{
    uint8 digest[20];
    uint32 clientSeed;
    uint16 clientBuild;
    std::string Account;
    WorldPacket addonsData;
};

struct AccountInfo
{
    uint32 Id;
    ::SessionKey SessionKey;
    std::string LastIP;
    bool IsLockedToIP;
    std::string LockCountry;
    uint8 Expansion;
    int64 MuteTime;
    LocaleConstant Locale;
    uint32 Recruiter;
    std::string OS;
    uint32 Flags;

    explicit AccountInfo(Field* fields)
    {
        //         0          1       2       3         4        5           6         7      8           9    10              11             12
        // SELECT id, sessionkey, last_ip, locked, lock_country, expansion, mutetime, locale, recruiter, os, flags, online_mute_timer, active_mute_id FROM account WHERE username = ?
        Id = fields[0].GetUInt32();
        SessionKey = HexStrToByteArray<SESSION_KEY_LENGTH>(std::string_view(fields[1].GetString())); 
        LastIP = fields[2].GetString();
        IsLockedToIP = fields[3].GetBool();
        LockCountry = fields[4].GetString();
        Expansion = fields[5].GetUInt8();
        MuteTime = fields[6].GetInt64();
        Locale = LocaleConstant(fields[7].GetUInt8());
        Recruiter = fields[8].GetUInt32();
        OS = fields[9].GetString();
        Flags = fields[10].GetUInt32();

        uint32 world_expansion = sWorld->getIntConfig(CONFIG_EXPANSION);
        if (Expansion > world_expansion)
            Expansion = world_expansion;

        if (Locale >= TOTAL_LOCALES)
            Locale = LOCALE_enUS;
    }
};

WorldSocket::ReadDataHandlerResult WorldSocket::ReadDataHandler()
{

    if (_initialized)
    {

        ClientPktHeader* header = reinterpret_cast<ClientPktHeader*>(_headerBuffer.GetReadPointer());
        OpcodeClient opcode = static_cast<OpcodeClient>(header->cmd);

        WorldPacket packet(opcode, std::move(_packetBuffer));
        WorldPacket* packetToQueue;

        if (sPacketLog->CanLogPacket())
            sPacketLog->LogPacket(packet, CLIENT_TO_SERVER, GetRemoteIpAddress(), GetRemotePort());

        std::unique_lock<std::mutex> sessionGuard(_worldSessionLock, std::defer_lock);

        switch (opcode)
        {
            case CMSG_PING:
            {
                LogOpcodeText(opcode, sessionGuard);
                try
                {
                    return HandlePing(packet) ? ReadDataHandlerResult::Ok : ReadDataHandlerResult::Error;
                }
                catch (ByteBufferException const&)
                {
                }
                TC_LOG_ERROR("network", "WorldSocket::ReadDataHandler(): client %s sent malformed CMSG_PING", GetRemoteIpAddress().to_string().c_str());
                return ReadDataHandlerResult::Error;
            }
            case CMSG_AUTH_SESSION:
            {
                LogOpcodeText(opcode, sessionGuard);
                if (_authed)
                {
                    // locking just to safely log offending user is probably overkill but we are disconnecting him anyway
                    if (sessionGuard.try_lock())
                        TC_LOG_ERROR("network", "WorldSocket::ProcessIncoming: received duplicate CMSG_AUTH_SESSION from %s", _worldSession->GetPlayerInfo().c_str());
                    return ReadDataHandlerResult::Error;
                }

                try
                {
                    HandleAuthSession(packet);
                    return ReadDataHandlerResult::Ok;
                    //return ReadDataHandlerResult::WaitingForQuery;
                }
                catch (ByteBufferException const&)
                {
                }
                TC_LOG_ERROR("network", "WorldSocket::ReadDataHandler(): client %s sent malformed CMSG_AUTH_SESSION", GetRemoteIpAddress().to_string().c_str());
                return ReadDataHandlerResult::Error;
            }
            case CMSG_KEEP_ALIVE: // todo: handle this packet in the same way of CMSG_TIME_SYNC_RESP
                sessionGuard.lock();
                LogOpcodeText(opcode, sessionGuard);
                if (_worldSession)
                {
                    _worldSession->ResetTimeOutTime(true);
                    return ReadDataHandlerResult::Ok;
                }
                TC_LOG_ERROR("network", "WorldSocket::ReadDataHandler: client %s sent CMSG_KEEP_ALIVE without being authenticated", GetRemoteIpAddress().to_string().c_str());
                return ReadDataHandlerResult::Error;

            case CMSG_LOG_DISCONNECT:
                packet.rfinish(); // contains uint32 disconnectReason;
                //sScriptMgr->OnPacketReceive(_worldSession, WorldPacket(*new_pct));
                DelayedCloseSocket();
                return ReadDataHandlerResult::Ok;

            case MSG_VERIFY_CONNECTIVITY:
            {
                //sScriptMgr->OnPacketReceive(_worldSession, WorldPacket(*new_pct));
                std::string str;
                packet >> str;
                if (str != "D OF WARCRAFT CONNECTION - CLIENT TO SERVER")
                    return ReadDataHandlerResult::Error;
                HandleSendAuthSession();
                return ReadDataHandlerResult::Ok;
            }

            case CMSG_TIME_SYNC_RESP:
                //packetToQueue = new WorldPacket(std::move(packet), std::chrono::steady_clock::now());
                //packetToQueue = new WorldPacket(packet, std::chrono::steady_clock::now());
                //packetToQueue = new WorldPacket(std::move(packet));
                packetToQueue = new WorldPacket(packet);
                break;

            default:
                packetToQueue = new WorldPacket(packet);
                break;
        }

        sessionGuard.lock();

        LogOpcodeText(opcode, sessionGuard);

        if (!_worldSession)
        {
            TC_LOG_ERROR("network.opcode", "ProcessIncoming: Client not authed opcode = %u", uint32(opcode));
            delete packetToQueue;
            return ReadDataHandlerResult::Error;
        }

        OpcodeHandler const* handler = clientOpcodeTable[opcode];
        //if (!handler)
        if (!handler || handler->Status == STATUS_UNHANDLED)
        {
            TC_LOG_ERROR("network.opcode", "No defined handler for opcode %s sent by %s", GetOpcodeNameForLogging(static_cast<OpcodeClient>(packet.GetOpcode()),false).c_str(), _worldSession->GetPlayerInfo().c_str());
            delete packetToQueue;
            //return ReadDataHandlerResult::Error;
            return ReadDataHandlerResult::Ok;
        }

        // Our Idle timer will reset on any non PING opcodes on login screen, allowing us to catch people idling.
        _worldSession->ResetTimeOutTime(false);

        // Copy the packet to the heap before enqueuing
        _worldSession->QueuePacket(packetToQueue);
    }
    else
    {
        std::string initializer(reinterpret_cast<char const*>(_packetBuffer.GetReadPointer()), std::min(_packetBuffer.GetActiveSize(), ClientConnectionInitialize.length()));
        if (initializer != ClientConnectionInitialize)
        {
            CloseSocket();
            return ReadDataHandlerResult::Error;
        }
        _initialized = true;
        _headerBuffer.Resize(sizeof(ClientPktHeader));
        _packetBuffer.Reset();
        HandleSendAuthSession();        
    }    
    return ReadDataHandlerResult::Ok;

}

void WorldSocket::LogOpcodeText(OpcodeClient opcode, std::unique_lock<std::mutex> const& guard) const
{
    if (!guard)
    {
        TC_LOG_TRACE("network.opcode", "C->S: %s %s", GetRemoteIpAddress().to_string().c_str(), GetOpcodeNameForLogging(opcode,false).c_str());
    }
    else
    {
        TC_LOG_TRACE("network.opcode", "C->S: %s %s", (_worldSession ? _worldSession->GetPlayerInfo() : GetRemoteIpAddress().to_string()).c_str(),
            GetOpcodeNameForLogging(opcode,false).c_str());
    }
}

void WorldSocket::SendPacketAndLogOpcode(WorldPacket const& packet)
{
    TC_LOG_TRACE("network.opcode", "S->C: %s %s", GetRemoteIpAddress().to_string().c_str(), GetOpcodeNameForLogging(static_cast<OpcodeServer>(packet.GetOpcode()),true).c_str());
    SendPacket(packet);
}

void WorldSocket::SendPacket(WorldPacket const& packet)
{
    if (!IsOpen())
        return;

    if (sPacketLog->CanLogPacket())
        sPacketLog->LogPacket(packet, SERVER_TO_CLIENT, GetRemoteIpAddress(), GetRemotePort());

    _bufferQueue.Enqueue(new EncryptablePacket(packet, _authCrypt.IsInitialized()));
}

void WorldSocket::HandleAuthSession(WorldPacket& recvPacket)
{
    std::shared_ptr<AuthSession> authSession = std::make_shared<AuthSession>();

    // recvPacket.read(authSession->AddonInfo.contents(), authSession->AddonInfo.size()); // .contents will throw if empty, thats what we want

    // // Get the account information from the auth database
    // LoginDatabasePreparedStatement* stmt = LoginDatabase.GetPreparedStatement(LOGIN_SEL_ACCOUNT_INFO_BY_NAME);
    // stmt->setInt32(0, int32(realm.Id.Realm));
    // stmt->setString(1, authSession->Account);

    uint32 addonSize;

    recvPacket.read_skip<uint32>();
    recvPacket.read_skip<uint32>();
    recvPacket >> authSession->digest[18];
    recvPacket >> authSession->digest[14];
    recvPacket >> authSession->digest[3];
    recvPacket >> authSession->digest[4];
    recvPacket >> authSession->digest[0];
    recvPacket.read_skip<uint32>();
    recvPacket >> authSession->digest[11];
    recvPacket >> authSession->clientSeed;
    recvPacket >> authSession->digest[19];
    recvPacket.read_skip<uint8>();
    recvPacket.read_skip<uint8>();
    recvPacket >> authSession->digest[2];
    recvPacket >> authSession->digest[9];
    recvPacket >> authSession->digest[12];
    recvPacket.read_skip<uint64>();
    recvPacket.read_skip<uint32>();
    recvPacket >> authSession->digest[16];
    recvPacket >> authSession->digest[5];
    recvPacket >> authSession->digest[6];
    recvPacket >> authSession->digest[8];
    recvPacket >> authSession->clientBuild;
    recvPacket >> authSession->digest[17];
    recvPacket >> authSession->digest[7];
    recvPacket >> authSession->digest[13];
    recvPacket >> authSession->digest[15];
    recvPacket >> authSession->digest[1];
    recvPacket >> authSession->digest[10];
    recvPacket >> addonSize;

    authSession->addonsData.resize(addonSize);
    recvPacket.read((uint8*)authSession->addonsData.contents(), addonSize);

    recvPacket.ReadBit();
    uint32 accountNameLength = recvPacket.ReadBits(11);

    authSession->Account = recvPacket.ReadString(accountNameLength);

    // if (sWorld->IsClosed())
    // {
    //     SendAuthResponseError(AUTH_REJECT);
    //     TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: World closed, denying client (%s).", GetRemoteAddress().c_str());
    //     return;
    // }

    // Get the account information from the realmd database
    //         0           1        2       3          4         5       6          7   8   9         10                    11
    // SELECT id, sessionkey, last_ip, locked, expansion, mutetime, locale, recruiter, os, flags, online_mute_timer, active_mute_id FROM account WHERE username = ?
    // size_t hashPos = authSession->account.find_last_of('#');
    LoginDatabasePreparedStatement* stmt = LoginDatabase.GetPreparedStatement(LOGIN_SEL_ACCOUNT_INFO_BY_NAME);
    stmt->setString(0, authSession->Account);

    //_queryProcessor.AddCallback(LoginDatabase.AsyncQuery(stmt).WithPreparedCallback(std::bind(&WorldSocket::HandleAuthSessionCallback, this, authSession, std::placeholders::_1)));
    PreparedQueryResult result = LoginDatabase.Query(stmt);
    HandleAuthSessionCallback(authSession,result);

}

void WorldSocket::HandleAuthSessionCallback(std::shared_ptr<AuthSession> authSession, PreparedQueryResult result)
{
    // // Stop if the account is not found
    // if (!result)
    // {
    //     // We can not log here, as we do not know the account. Thus, no accountId.
    //     SendAuthResponseError(AUTH_UNKNOWN_ACCOUNT);
    //     TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Sent Auth Response (unknown account).");
    //     DelayedCloseSocket();
    //     return;
    // }

    // AccountInfo account(result->Fetch());

    // // For hook purposes, we get Remoteaddress at this point.
    // std::string address = GetRemoteIpAddress().to_string();

    // LoginDatabasePreparedStatement* stmt = nullptr;

    // if (sWorld->getBoolConfig(CONFIG_ALLOW_LOGGING_IP_ADDRESSES_IN_DATABASE))
    // {
    //     // As we don't know if attempted login process by ip works, we update last_attempt_ip right away
    //     stmt = LoginDatabase.GetPreparedStatement(LOGIN_UPD_LAST_ATTEMPT_IP);
    //     stmt->setString(0, address);
    //     stmt->setString(1, authSession->Account);
    //     LoginDatabase.Execute(stmt);
    //     // This also allows to check for possible "hack" attempts on account
    // }

    // // even if auth credentials are bad, try using the session key we have - client cannot read auth response error without it
    // _authCrypt.Init(account.SessionKey);

    // // First reject the connection if packet contains invalid data or realm state doesn't allow logging in
    // if (sWorld->IsClosed())
    // {
    //     SendAuthResponseError(AUTH_REJECT);
    //     TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: World closed, denying client (%s).", GetRemoteIpAddress().to_string().c_str());
    //     DelayedCloseSocket();
    //     return;
    // }

    // if (authSession->RealmID != realm.Id.Realm)
    // {
    //     SendAuthResponseError(REALM_LIST_REALM_NOT_FOUND);
    //     TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Client %s requested connecting with realm id %u but this realm has id %u set in config.",
    //         GetRemoteIpAddress().to_string().c_str(), authSession->RealmID, realm.Id.Realm);
    //     DelayedCloseSocket();
    //     return;
    // }

    // // Must be done before WorldSession is created
    // bool wardenActive = sWorld->getBoolConfig(CONFIG_WARDEN_ENABLED);
    // if (wardenActive && account.OS != "Win" && account.OS != "OSX")
    // {
    //     SendAuthResponseError(AUTH_REJECT);
    //     TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Client %s attempted to log in using invalid client OS (%s).", address.c_str(), account.OS.c_str());
    //     DelayedCloseSocket();
    //     return;
    // }

    // // Check that Key and account name are the same on client and server
    // uint8 t[4] = { 0x00,0x00,0x00,0x00 };

    // Trinity::Crypto::SHA1 sha;
    // sha.UpdateData(authSession->Account);
    // sha.UpdateData(t);
    // sha.UpdateData(authSession->LocalChallenge);
    // sha.UpdateData(_authSeed);
    // sha.UpdateData(account.SessionKey);
    // sha.Finalize();

    // if (sha.GetDigest() != authSession->Digest)
    // {
    //     SendAuthResponseError(AUTH_FAILED);
    //     TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Authentication failed for account: %u ('%s') address: %s", account.Id, authSession->Account.c_str(), address.c_str());
    //     DelayedCloseSocket();
    //     return;
    // }

    // if (IpLocationRecord const* location = sIPLocation->GetLocationRecord(address))
    //     _ipCountry = location->CountryCode;

    // ///- Re-check ip locking (same check as in auth).
    // if (account.IsLockedToIP)
    // {
    //     if (account.LastIP != address)
    //     {
    //         SendAuthResponseError(AUTH_FAILED);
    //         TC_LOG_DEBUG("network", "WorldSocket::HandleAuthSession: Sent Auth Response (Account IP differs. Original IP: %s, new IP: %s).", account.LastIP.c_str(), address.c_str());
    //         // We could log on hook only instead of an additional db log, however action logger is config based. Better keep DB logging as well
    //         sScriptMgr->OnFailedAccountLogin(account.Id);
    //         DelayedCloseSocket();
    //         return;
    //     }
    // }
    // else if (!account.LockCountry.empty() && account.LockCountry != "00" && !_ipCountry.empty())
    // {
    //     if (account.LockCountry != _ipCountry)
    //     {
    //         SendAuthResponseError(AUTH_FAILED);
    //         TC_LOG_DEBUG("network", "WorldSocket::HandleAuthSession: Sent Auth Response (Account country differs. Original country: %s, new country: %s).", account.LockCountry.c_str(), _ipCountry.c_str());
    //         // We could log on hook only instead of an additional db log, however action logger is config based. Better keep DB logging as well
    //         sScriptMgr->OnFailedAccountLogin(account.Id);
    //         DelayedCloseSocket();
    //         return;
    //     }
    // }

    // int64 mutetime = account.MuteTime;
    // //! Negative mutetime indicates amount of seconds to be muted effective on next login - which is now.
    // if (mutetime < 0)
    // {
    //     mutetime = GameTime::GetGameTime() + llabs(mutetime);

    //     stmt = LoginDatabase.GetPreparedStatement(LOGIN_UPD_MUTE_TIME_LOGIN);
    //     stmt->setInt64(0, mutetime);
    //     stmt->setUInt32(1, account.Id);
    //     LoginDatabase.Execute(stmt);
    // }

    // if (account.IsBanned)
    // {
    //     SendAuthResponseError(AUTH_BANNED);
    //     TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Sent Auth Response (Account banned).");
    //     sScriptMgr->OnFailedAccountLogin(account.Id);
    //     DelayedCloseSocket();
    //     return;
    // }

    // // Check locked state for server
    // AccountTypes allowedAccountType = sWorld->GetPlayerSecurityLimit();
    // TC_LOG_DEBUG("network", "Allowed Level: %u Player Level %u", allowedAccountType, account.Security);
    // if (allowedAccountType > SEC_PLAYER && account.Security < allowedAccountType)
    // {
    //     SendAuthResponseError(AUTH_UNAVAILABLE);
    //     TC_LOG_DEBUG("network", "WorldSocket::HandleAuthSession: User tries to login but his security level is not enough");
    //     sScriptMgr->OnFailedAccountLogin(account.Id);
    //     DelayedCloseSocket();
    //     return;
    // }

    // TC_LOG_DEBUG("network", "WorldSocket::HandleAuthSession: Client '%s' authenticated successfully from %s.", authSession->Account.c_str(), address.c_str());

    // if (sWorld->getBoolConfig(CONFIG_ALLOW_LOGGING_IP_ADDRESSES_IN_DATABASE))
    // {
    //     // Update the last_ip in the database as it was successful for login
    //     stmt = LoginDatabase.GetPreparedStatement(LOGIN_UPD_LAST_IP);

    //     stmt->setString(0, address);
    //     stmt->setString(1, authSession->Account);

    //     LoginDatabase.Execute(stmt);
    // }

    // // At this point, we can safely hook a successful login
    // sScriptMgr->OnAccountLogin(account.Id);

    // _authed = true;
    // _worldSession = new WorldSession(account.Id, std::move(authSession->Account), shared_from_this(), account.Security,
    //     account.Expansion, mutetime, account.Locale, account.Recruiter, account.IsRectuiter);
    // _worldSession->ReadAddonsInfo(authSession->AddonInfo);

    // // Initialize Warden system only if it is enabled by config
    // if (wardenActive)
    //     _worldSession->InitWarden(account.SessionKey, account.OS);

    //_queryProcessor.AddCallback(_worldSession->LoadPermissionsAsync().WithPreparedCallback(std::bind(&WorldSocket::LoadSessionPermissionsCallback, this, std::placeholders::_1)));
    

    // Stop if the account is not found
    if (!result)
    {
        SendAuthResponseError(AUTH_UNKNOWN_ACCOUNT);
        TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Sent Auth Response (unknown account).");
        DelayedCloseSocket();
        return;
    }

    AccountInfo account(result->Fetch());

    ///- Re-check ip locking (same check as in realmd).
    if (account.IsLockedToIP) // if ip is locked
    {
        if (strcmp (account.LastIP.c_str(), GetRemoteIpAddress().to_string().c_str()))
        {
            SendAuthResponseError(AUTH_FAILED);
            TC_LOG_DEBUG("network", "WorldSocket::HandleAuthSession: Sent Auth Response (Account IP differs).");
            DelayedCloseSocket();
            return;
        }
    }

    BigNumber k;
    // k.SetHexStr(fields[1].GetCString());

    // Must be done before WorldSession is created
    if (sWorld->getBoolConfig(CONFIG_WARDEN_ENABLED) && account.OS != "Win" && account.OS != "Wn64" && account.OS != "OSX")
    {
        SendAuthResponseError(AUTH_REJECT);
        TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Client %s attempted to log in using invalid client OS (%s).", GetRemoteIpAddress().to_string().c_str(), account.OS.c_str());
        DelayedCloseSocket();
        return;
    }

    // get boost info
    LoginDatabasePreparedStatement* stmt = LoginDatabase.GetPreparedStatement(LOGIN_SEL_ACCOUNT_BOOST);
    stmt->setUInt32(0, account.Id);
    stmt->setUInt32(1, realm.Id.Realm);

    bool hasBoost = false;
    if (LoginDatabase.Query(stmt))
        hasBoost = true;

    // Get mute info
    std::string mutedBy = "";
    std::string muteReason = "";
    bool mutedInPublicChannelsOnly = false;
    uint32 onlineMuteTimer = 0;

    Field* fields;// = result->Fetch();
    if (auto muteRes = LoginDatabase.PQuery("SELECT am.muted_by, am.mute_reason, am.public_channels_only, m.mute_timer FROM mute_active AS m, account_muted AS am WHERE m.realmid = '%u' AND m.account = '%u' AND m.mute_id = am.id AND m.realmid = am.realmid", realm.Id.Realm, account.Id))
    {
        fields = muteRes->Fetch();
        mutedBy = fields[0].GetString();
        muteReason = fields[1].GetString();
        mutedInPublicChannelsOnly = fields[2].GetBool();
        onlineMuteTimer = fields[3].GetUInt32();
    }

    // Checks gmlevel per Realm
    stmt = LoginDatabase.GetPreparedStatement(LOGIN_GET_GMLEVEL_BY_REALMID);

    stmt->setUInt32(0, account.Id);
    stmt->setInt32(1, int32(realm.Id.Realm));

    result = LoginDatabase.Query(stmt);

    uint8 security;
    if (!result)
        security = 0;
    else
    {
        fields = result->Fetch();
        security = fields[0].GetUInt8();
    }

    // Re-check account ban (same check as in realmd)
    stmt = LoginDatabase.GetPreparedStatement(LOGIN_SEL_BANS);

    stmt->setUInt32(0, account.Id);
    //stmt->setString(1, GetRemoteAddress());
    stmt->setString(1, GetRemoteIpAddress().to_string().c_str());
    

    PreparedQueryResult banresult = LoginDatabase.Query(stmt);

    if (banresult) // if account banned
    {
        SendAuthResponseError(AUTH_BANNED);
        TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Sent Auth Response (Account banned).");
        DelayedCloseSocket();
        return;
    }

    // Check locked state for server
    AccountTypes allowedAccountType = sWorld->GetPlayerSecurityLimit();
    TC_LOG_DEBUG("network", "Allowed Level: %u Player Level %u", allowedAccountType, AccountTypes(security));
    if (allowedAccountType > SEC_PLAYER && AccountTypes(security) < allowedAccountType)
    {
        SendAuthResponseError(AUTH_UNAVAILABLE);
        TC_LOG_INFO("network", "WorldSocket::HandleAuthSession: User tries to login but his security level is not enough");
        DelayedCloseSocket();
        return;
    }

    // Check that Key and account name are the same on client and server
    uint8 t[4] = { 0x00,0x00,0x00,0x00 };

    Trinity::Crypto::SHA1 sha;
    sha.UpdateData(authSession->Account);
    sha.UpdateData(t);
    //sha.UpdateData(authSession->clientSeed);
    sha.UpdateData((uint8*)&authSession->clientSeed, 4);
    sha.UpdateData(_authSeed);
    sha.UpdateData(account.SessionKey);
    sha.Finalize();

    std::string address = GetRemoteIpAddress().to_string();

    if (memcmp(sha.GetDigest().data(), authSession->digest, 20)) //(sha.GetDigest() != authSession->digest) //if (memcmp(sha.GetDigest(), authSession->digest, 20))
    {
        SendAuthResponseError(AUTH_FAILED);
        TC_LOG_ERROR("network", "WorldSocket::HandleAuthSession: Authentication failed for account: %u ('%s') address: %s", account.Id, authSession->Account.c_str(), address.c_str());
        DelayedCloseSocket();
        return;
    }

    if (IpLocationRecord const* location = sIPLocation->GetLocationRecord(address))
        _ipCountry = location->CountryCode;


    TC_LOG_DEBUG("network", "WorldSocket::HandleAuthSession: Client '%s' authenticated successfully from %s.",
        authSession->Account.c_str(),
        address.c_str());

    // Check if this user is by any chance a recruiter
    stmt = LoginDatabase.GetPreparedStatement(LOGIN_SEL_ACCOUNT_RECRUITER);
    stmt->setUInt32(0, account.Id);
    result = LoginDatabase.Query(stmt);

    bool isRecruiter = false;
    if (result)
        isRecruiter = true;

    // Update the last_ip in the database

    stmt = LoginDatabase.GetPreparedStatement(LOGIN_UPD_LAST_IP);
    stmt->setString(0, address);
    stmt->setString(1, authSession->Account);
    LoginDatabase.Execute(stmt);

    _authCrypt.Init(account.SessionKey);
    _headerBuffer.Resize(sizeof(WorldClientPktHeader));

    // NOTE ATM the socket is single-threaded, have this in mind ...
    //ACE_NEW_RETURN(_worldSession, WorldSession(account.Id, this, AccountTypes(security), account.Expansion, account.MuteTime, account.Locale, account.Recruiter, account.Flags, isRecruiter, hasBoost), -1);
    _worldSession = new WorldSession(account.Id, shared_from_this(), AccountTypes(security), account.Expansion, account.MuteTime, account.Locale, account.Recruiter, account.Flags, isRecruiter, hasBoost);
    _worldSession->SetMute({ onlineMuteTimer, mutedBy, muteReason, mutedInPublicChannelsOnly });

    _worldSession->LoadGlobalAccountData();
    _worldSession->LoadTutorialsData();
    _worldSession->ReadAddonsInfo(authSession->addonsData);
    // Initialize Warden system only if it is enabled by config
    if (sWorld->getBoolConfig(CONFIG_WARDEN_ENABLED))
        _worldSession->InitWarden(&k, account.OS);

    // Sleep this Network thread for
    uint32 sleepTime = sWorld->getIntConfig(CONFIG_SESSION_ADD_DELAY);
    std::this_thread::sleep_for(Microseconds(sleepTime));
    sWorld->AddSession(_worldSession);

    //_queryProcessor.AddCallback(_worldSession->LoadPermissionsAsync().WithPreparedCallback(std::bind(&WorldSocket::LoadSessionPermissionsCallback, this, std::placeholders::_1)));
    
    // AsyncRead();
}

void WorldSocket::LoadSessionPermissionsCallback(PreparedQueryResult result)
{
    // RBAC must be loaded before adding session to check for skip queue permission
    //_worldSession->GetRBACData()->LoadFromDBCallback(result);

    //sWorld->AddSession(_worldSession);
}

void WorldSocket::SendAuthResponseError(uint8 code)
{
    WorldPacket packet(SMSG_AUTH_RESPONSE, 1);
    packet.WriteBit(0); // has account info
    packet.WriteBit(0); // has queue info
    packet.FlushBits();
    packet << uint8(code);

    SendPacketAndLogOpcode(packet);
}

bool WorldSocket::HandlePing(WorldPacket& recvPacket)
{
    using namespace std::chrono;

    uint32 ping;
    uint32 latency;

    // Get the ping packet content
    recvPacket >> ping;
    recvPacket >> latency;

    if (_LastPingTime == steady_clock::time_point())
    {
        _LastPingTime = steady_clock::now();
    }
    else
    {
        steady_clock::time_point now = steady_clock::now();

        steady_clock::duration diff = now - _LastPingTime;

        _LastPingTime = now;

        if (diff < seconds(27))
        {
            ++_OverSpeedPings;

            uint32 maxAllowed = sWorld->getIntConfig(CONFIG_MAX_OVERSPEED_PINGS);

            if (maxAllowed && _OverSpeedPings > maxAllowed)
            {
                std::unique_lock<std::mutex> sessionGuard(_worldSessionLock);

                //if (_worldSession && !_worldSession->HasPermission(rbac::RBAC_PERM_SKIP_CHECK_OVERSPEED_PING))
                if (_worldSession && _worldSession->GetSecurity() == SEC_PLAYER)
                {
                    TC_LOG_ERROR("network", "WorldSocket::HandlePing: %s kicked for over-speed pings (address: %s)",
                        _worldSession->GetPlayerInfo().c_str(), GetRemoteIpAddress().to_string().c_str());

                    return false;
                }
            }
        }
        else
            _OverSpeedPings = 0;
    }

    {
        std::lock_guard<std::mutex> sessionGuard(_worldSessionLock);

        if (_worldSession)
            _worldSession->SetLatency(latency);
        else
        {
            TC_LOG_ERROR("network", "WorldSocket::HandlePing: peer sent CMSG_PING, but is not authenticated or got recently kicked, address = %s", GetRemoteIpAddress().to_string().c_str());
            return false;
        }
    }

    WorldPacket packet(SMSG_PONG, 4);
    packet << ping;
    SendPacketAndLogOpcode(packet);
    return true;
}
