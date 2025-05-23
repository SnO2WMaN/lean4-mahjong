namespace Mahjong
namespace Tile

inductive Num.Suit where
  | man -- 萬子
  | pin -- 筒子
  | sou -- 索子
  deriving Inhabited, DecidableEq

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
  deriving Inhabited, DecidableEq

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

theorem eq_prev_next (d : Digit) : d.prev.next = d := by
  cases d <;> simp [Digit.prev, Digit.next]

theorem prev_not1_neq_9 (d : Digit) (h : d ≠ .n1): d.prev ≠ .n9 := by
  cases d; repeat (first | contradiction | simp [Digit.prev])
theorem next_not9_neq_1 (d : Digit) (h : d ≠ .n9): d.next ≠ .n1 := by
  cases d; repeat (first | contradiction | simp [Digit.next])

end Num.Digit

/-- 数牌 -/
structure Num where
  suit : Num.Suit
  digit : Num.Digit
  deriving Inhabited, DecidableEq

instance : ToString Num where
  toString n := s!"{n.digit}{n.suit}"

namespace Num


structure Not1 extends Num where
  not1 : digit ≠ .n1 := by simp

structure Not9 extends Num where
  not9 : digit ≠ .n9 := by simp

structure Not19 extends Num, Not1, Not9 where
instance : ToString Not19 where
  toString n := toString n.toNum

instance : ToString Not1 where toString n := toString n.toNum
instance : Coe Not1 Num where coe n := { suit := n.suit, digit := n.digit }
instance : Coe Not19 Not1 where coe n := { suit := n.suit, digit := n.digit, not1 := n.not1 }
protected def Not1.prev (n : Not1) : Not9 := {
  suit := n.suit,
  digit := n.digit.prev,
  not9 := Digit.prev_not1_neq_9 n.digit n.not1
}

instance : ToString Not9 where toString n := toString n.toNum
instance : Coe Not9 Num where coe n := { suit := n.suit, digit := n.digit }
instance : Coe Not19 Not9 where coe n := { suit := n.suit, digit := n.digit, not9 := n.not9 }
protected def Not9.next (n : Not9) : Not1 := {
  suit := n.suit,
  digit := n.digit.next,
  not1 := Digit.next_not9_neq_1 n.digit n.not9
}

def M1 : Num.Not9  := { suit := .man, digit := .n1 }
def M2 : Num.Not19 := { suit := .man, digit := .n2 }
def M3 : Num.Not19 := { suit := .man, digit := .n3 }
def M4 : Num.Not19 := { suit := .man, digit := .n4 }
def M5 : Num.Not19 := { suit := .man, digit := .n5 }
def M6 : Num.Not19 := { suit := .man, digit := .n6 }
def M7 : Num.Not19 := { suit := .man, digit := .n7 }
def M8 : Num.Not19 := { suit := .man, digit := .n8 }
def M9 : Num.Not1  := { suit := .man, digit := .n9 }

def P1 : Num.Not9  := { suit := .pin, digit := .n1 }
def P2 : Num.Not19 := { suit := .pin, digit := .n2 }
def P3 : Num.Not19 := { suit := .pin, digit := .n3 }
def P4 : Num.Not19 := { suit := .pin, digit := .n4 }
def P5 : Num.Not19 := { suit := .pin, digit := .n5 }
def P6 : Num.Not19 := { suit := .pin, digit := .n6 }
def P7 : Num.Not19 := { suit := .pin, digit := .n7 }
def P8 : Num.Not19 := { suit := .pin, digit := .n8 }
def P9 : Num.Not1  := { suit := .pin, digit := .n9 }

def S1 : Num.Not9  := { suit := .sou, digit := .n1 }
def S2 : Num.Not19 := { suit := .sou, digit := .n2 }
def S3 : Num.Not19 := { suit := .sou, digit := .n3 }
def S4 : Num.Not19 := { suit := .sou, digit := .n4 }
def S5 : Num.Not19 := { suit := .sou, digit := .n5 }
def S6 : Num.Not19 := { suit := .sou, digit := .n6 }
def S7 : Num.Not19 := { suit := .sou, digit := .n7 }
def S8 : Num.Not19 := { suit := .sou, digit := .n8 }
def S9 : Num.Not1  := { suit := .sou, digit := .n9 }

end Num

/-- 風牌 -/
inductive Wind
  | east -- 東
  | south -- 南
  | west -- 西
  | north -- 北
  deriving Inhabited, DecidableEq

instance : ToString Wind where
  toString w := match w with
    | .east => "東"
    | .south => "南"
    | .west => "西"
    | .north => "北"

namespace Wind
protected def next : Wind → Wind
  | .east => .south
  | .south => .west
  | .west => .north
  | .north => .east
protected def prev : Wind → Wind
  | .east => .north
  | .south => .east
  | .west => .south
  | .north => .west
theorem eq_prev_next (w : Wind) : w.prev.next = w := by
  cases w <;> simp [Wind.prev, Wind.next]
end Wind

/-- 字牌 -/
inductive Dragon
  | white -- 白
  | green -- 發
  | red -- 中
  deriving Inhabited, DecidableEq

instance : ToString Dragon where
  toString d := match d with
    | .white => "白"
    | .green => "發"
    | .red => "中"

namespace Dragon
protected def next : Dragon → Dragon
  | .white => .green
  | .green => .red
  | .red => .white
protected def prev : Dragon → Dragon
  | .white => .red
  | .green => .white
  | .red => .green
theorem eq_prev_next (d : Dragon) : d.prev.next = d := by
  cases d <;> simp [Dragon.prev, Dragon.next]
end Dragon

open Num.Suit Num.Digit

inductive Tile where
  | num (n: Num)
  | wind (w: Wind)
  | dragon (d: Dragon)
  deriving Inhabited, DecidableEq

instance : ToString Tile where
  toString tile := match tile with
    | .num n => toString n
    | .wind w => toString w
    | .dragon d => toString d

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
