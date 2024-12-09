/- Game state -/
import Mahjong.Definition

namespace Mahjong

structure Hand where
  tiles: Array Tile
  size_p: tiles.size = 13

structure State where
  player_n: Hand
  player_w: Hand
  player_e: Hand
  player_s: Hand


end Mahjong
