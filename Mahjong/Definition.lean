namespace Mahjong
namespace Tile

inductive Num.Suit where
  | man -- 萬子
  | pin -- 筒子
  | sou -- 索子
  deriving Inhabited

instance : ToString Num.Suit where
  toString suit := match suit with
    | .man => "萬"
    | .pin => "筒"
    | .sou => "索"

inductive Num.Digit where
  | n1
  | n2
  | n3
  | n4
  | n5
  | n6
  | n7
  | n8
  | n9
  deriving Inhabited

instance : ToString Num.Digit where
  toString d := match d with
    | .n1 => "一"
    | .n2 => "二"
    | .n3 => "三"
    | .n4 => "四"
    | .n5 => "五"
    | .n6 => "六"
    | .n7 => "七"
    | .n8 => "八"
    | .n9 => "九"
instance : OfNat Num.Digit n where
  ofNat := match n with
    | 1 => .n1
    | 2 => .n2
    | 3 => .n3
    | 4 => .n3
    | 5 => .n5
    | 6 => .n6
    | 7 => .n7
    | 8 => .n8
    | 9 => .n9
    | _ => panic! "Invalid number tile {n}"

namespace Num.Digit

protected def prev : Num.Digit → Num.Digit
  | n1 => n9
  | n2 => n1
  | n3 => n2
  | n4 => n3
  | n5 => n4
  | n6 => n5
  | n7 => n6
  | n8 => n7
  | n9 => n8

protected def next : Num.Digit → Num.Digit
  | n1 => n2
  | n2 => n3
  | n3 => n4
  | n4 => n5
  | n5 => n6
  | n6 => n7
  | n7 => n8
  | n8 => n9
  | n9 => n1

theorem eq_ring_prev_next (d : Digit) : d.prev.next = d := by
  cases d <;> simp [Digit.prev, Digit.next]

theorem ring_prev_not1_neq_9 (d : Digit) (h : d ≠ .n1): d.prev ≠ .n9 := by
  cases d; repeat (first | contradiction | simp [Digit.prev])
theorem ring_next_not9_neq_1 (d : Digit) (h : d ≠ .n9): d.next ≠ .n1 := by
  cases d; repeat (first | contradiction | simp [Digit.next])

end Num.Digit

/-- 数牌 -/
structure Num where
  suit : Num.Suit
  digit : Num.Digit

instance : ToString Num where
  toString n := s!"{n.digit}{n.suit}"

namespace Num

structure Not19 extends Num where
  not1 : digit ≠ .n1
  not9 : digit ≠ .n9
instance : ToString Not19 where
  toString n := toString n.toNum

structure Not1 extends Num where
  not1 : digit ≠ .n1

structure Not9 extends Num where
  not9 : digit ≠ .n9

instance : ToString Not1 where toString n := toString n.toNum
instance : Coe Not1 Num where coe n := { suit := n.suit, digit := n.digit }
instance : Coe Not19 Not1 where coe n := { suit := n.suit, digit := n.digit, not1 := n.not1 }
protected def Not1.prev (n : Not1) : Not9 := {
  suit := n.suit,
  digit := n.digit.prev,
  not9 := Digit.ring_prev_not1_neq_9 n.digit n.not1
  }

instance : ToString Not9 where toString n := toString n.toNum
instance : Coe Not9 Num where coe n := { suit := n.suit, digit := n.digit }
instance : Coe Not19 Not9 where coe n := { suit := n.suit, digit := n.digit, not9 := n.not9 }
protected def Not9.next (n : Not9) : Not1 := {
  suit := n.suit,
  digit := n.digit.next,
  not1 := Digit.ring_next_not9_neq_1 n.digit n.not9
  }

def M1 : Num.Not9  := { suit := .man, digit := .n1, not9 := by simp }
def M2 : Num.Not19 := { suit := .man, digit := .n2, not1 := by simp, not9 := by simp }
def M3 : Num.Not19 := { suit := .man, digit := .n3, not1 := by simp, not9 := by simp }
def M4 : Num.Not19 := { suit := .man, digit := .n4, not1 := by simp, not9 := by simp }
def M5 : Num.Not19 := { suit := .man, digit := .n5, not1 := by simp, not9 := by simp }
def M6 : Num.Not19 := { suit := .man, digit := .n6, not1 := by simp, not9 := by simp }
def M7 : Num.Not19 := { suit := .man, digit := .n7, not1 := by simp, not9 := by simp }
def M8 : Num.Not19 := { suit := .man, digit := .n8, not1 := by simp, not9 := by simp }
def M9 : Num.Not1  := { suit := .man, digit := .n9, not1 := by simp }

def P1 : Num.Not9  := { suit := .pin, digit := .n1, not9 := by simp }
def P2 : Num.Not19 := { suit := .pin, digit := .n2, not1 := by simp, not9 := by simp }
def P3 : Num.Not19 := { suit := .pin, digit := .n3, not1 := by simp, not9 := by simp }
def P4 : Num.Not19 := { suit := .pin, digit := .n4, not1 := by simp, not9 := by simp }
def P5 : Num.Not19 := { suit := .pin, digit := .n5, not1 := by simp, not9 := by simp }
def P6 : Num.Not19 := { suit := .pin, digit := .n6, not1 := by simp, not9 := by simp }
def P7 : Num.Not19 := { suit := .pin, digit := .n7, not1 := by simp, not9 := by simp }
def P8 : Num.Not19 := { suit := .pin, digit := .n8, not1 := by simp, not9 := by simp }
def P9 : Num.Not1  := { suit := .pin, digit := .n9, not1 := by simp }

def S1 : Num.Not9  := { suit := .sou, digit := .n1, not9 := by simp }
def S2 : Num.Not19 := { suit := .sou, digit := .n2, not1 := by simp, not9 := by simp }
def S3 : Num.Not19 := { suit := .sou, digit := .n3, not1 := by simp, not9 := by simp }
def S4 : Num.Not19 := { suit := .sou, digit := .n4, not1 := by simp, not9 := by simp }
def S5 : Num.Not19 := { suit := .sou, digit := .n5, not1 := by simp, not9 := by simp }
def S6 : Num.Not19 := { suit := .sou, digit := .n6, not1 := by simp, not9 := by simp }
def S7 : Num.Not19 := { suit := .sou, digit := .n7, not1 := by simp, not9 := by simp }
def S8 : Num.Not19 := { suit := .sou, digit := .n8, not1 := by simp, not9 := by simp }
def S9 : Num.Not1  := { suit := .sou, digit := .n9, not1 := by simp }

end Num

/-- 風牌 -/
inductive Wind
  | north -- 北
  | west -- 西
  | south -- 南
  | east -- 東

instance : ToString Wind where
  toString w := match w with
    | .west => "西"
    | .east => "東"
    | .north => "北"
    | .south => "南"

/-- 字牌 -/
inductive Dragon
| red -- 中
| green -- 發
| white -- 白

instance : ToString Dragon where
  toString d := match d with
    | .red => "中"
    | .green => "發"
    | .white => "白"

open Num.Suit Num.Digit

inductive Tile where
  | num (n: Num)
  | wind (w: Wind)
  | dragon (d: Dragon)

end Tile

export Tile (Tile)

namespace Hand

open Tile Num Dragon

def dragon3 (d : Dragon) := [d, d, d]

def wind3 (w : Wind) := [w, w, w]

/-- 順子 -/
def shuntsu (n : Not19) := ([Not1.prev n, n, Not9.next n] : List Num)
def kotsu (n : Num) := [n, n, n]

abbrev Tile : Type := Num

end Hand

end Mahjong
