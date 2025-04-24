import Mahjong.Definition

namespace Mahjong

structure Hand where
  tiles : Array Tile
  size_p : tiles.size = 13

structure Player where
  hand : Hand
  discards : List Tile

structure Wall where
  tiles : List Tile

/-- Game state -/
structure State where
  wall : Wall
  player_n : Player
  player_w : Player
  player_e : Player
  player_s : Player

protected def State.getWindPlayer (state : State) : Tile.Wind → Player
  | .north => state.player_n
  | .west => state.player_w
  | .east => state.player_e
  | .south => state.player_s

end Mahjong
