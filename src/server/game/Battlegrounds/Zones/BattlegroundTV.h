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

#ifndef BATTLEGROUND_TV_H
#define BATTLEGROUND_TV_H

#include "Battleground.h"

enum BattlegroundTVObjectTypes
{
    BG_TV_OBJECT_DOOR_1         = 0,
    BG_TV_OBJECT_DOOR_2         = 1,
    BG_TV_OBJECT_BUFF_1         = 2,
    BG_TV_OBJECT_BUFF_2         = 3,
    BG_TV_OBJECT_MAX            = 4
};

enum BattlegroundTVObjects
{
    BG_TV_OBJECT_TYPE_DOOR_1    = 213196,
    BG_TV_OBJECT_TYPE_DOOR_2    = 213197,
    BG_TV_OBJECT_TYPE_BUFF_1    = 184663,
    BG_TV_OBJECT_TYPE_BUFF_2    = 184664
};

struct BattlegroundTVScore : public BattlegroundScore
{
};

class BattlegroundTV : public Battleground
{
public:
    BattlegroundTV();
    ~BattlegroundTV();

    /* inherited from BattlegroundClass */
    void AddPlayer(Player* player) override;
    void OnInvite(Player* player, GroupQueueInfo const* ginfo) override;
    void StartingEventCloseDoors() override;
    void StartingEventOpenDoors() override;

    void RemovePlayer(Player* player, uint64 guid, uint32 team) override;
    void HandleAreaTrigger(Player* Source, uint32 Trigger) override;
    bool SetupBattleground() override;
    void Reset() override;
    void FillInitialWorldStates(WorldStateBuilder& builder) override;
    void HandleKillPlayer(Player* player, Player* killer) override;
    bool HandlePlayerUnderMap(Player* player) override;
};
#endif
