namespace Mahjong
namespace Tile

inductive Num.Suit : Type
| M -- 萬子
| P -- 筒子
| S -- 索子
def Num.Suit.toString : Num.Suit → String
| M => "萬"
| P => "筒"
| S => "索"
instance : ToString Num.Suit where toString := Num.Suit.toString

inductive Num.Digit : Type
| one
| two
| three
| four
| five
| six
| seven
| eight
| nine

namespace Num.Digit

def toString : Num.Digit → String
| one => "一"
| two => "二"
| three => "三"
| four => "四"
| five => "五"
| six => "六"
| seven => "七"
| eight => "八"
| nine => "九"
instance : ToString Num.Digit where toString := toString

def ring_prev
  | one   => nine
  | two   => one
  | three => two
  | four  => three
  | five  => four
  | six   => five
  | seven => six
  | eight => seven
  | nine  => eight

def ring_next
  | one   => two
  | two   => three
  | three => four
  | four  => five
  | five  => six
  | six   => seven
  | seven => eight
  | eight => nine
  | nine  => one

theorem eq_ring_prev_next (d : Digit) : d.ring_prev.ring_next = d :=
  by
    cases d
    all_goals
      simp [ring_prev, ring_next]

theorem ring_prev_not1_neq_9 (d : Digit) (h : d ≠ one): d.ring_prev ≠ nine := by cases d; repeat (first | contradiction | simp [ring_prev])
theorem ring_next_not9_neq_1 (d : Digit) (h : d ≠ nine): d.ring_next ≠ one := by cases d; repeat (first | contradiction | simp [ring_next])

end Num.Digit

/-- 数牌 -/
structure Num where
  suit : Num.Suit
  digit : Num.Digit

namespace Num

def toString (n : Num) : String := s!"{n.digit}{n.suit}"
instance : ToString Num where toString := Num.toString

open Num.Suit Num.Digit

structure Not19 extends Num where
  not1 : digit ≠ one
  not9 : digit ≠ nine
instance : ToString Not19 where toString n := n.toString

structure Not1 extends Num where
  not1 : digit ≠ one

structure Not9 extends Num where
  not9 : digit ≠ nine

instance : ToString Not1 where toString n := n.toString
instance : Coe Not1 Num where coe n := { suit := n.suit, digit := n.digit }
instance : Coe Not19 Not1 where coe n := { suit := n.suit, digit := n.digit, not1 := n.not1 }
def Not1.prev (n : Not1) : Not9 := { suit := n.suit, digit := n.digit.ring_prev, not9 := ring_prev_not1_neq_9 n.digit n.not1 }

instance : ToString Not9 where toString n := n.toString
instance : Coe Not9 Num where coe n := { suit := n.suit, digit := n.digit }
instance : Coe Not19 Not9 where coe n := { suit := n.suit, digit := n.digit, not9 := n.not9 }
def Not9.next (n : Not9) : Not1 := { suit := n.suit, digit := n.digit.ring_next, not1 := ring_next_not9_neq_1 n.digit n.not9 }

def M1 : Num.Not9  := { suit := M, digit := one, not9 := by simp }
def M2 : Num.Not19 := { suit := M, digit := two, not1 := by simp, not9 := by simp }
def M3 : Num.Not19 := { suit := M, digit := three, not1 := by simp, not9 := by simp }
def M4 : Num.Not19 := { suit := M, digit := four, not1 := by simp, not9 := by simp }
def M5 : Num.Not19 := { suit := M, digit := five, not1 := by simp, not9 := by simp }
def M6 : Num.Not19 := { suit := M, digit := six, not1 := by simp, not9 := by simp }
def M7 : Num.Not19 := { suit := M, digit := seven, not1 := by simp, not9 := by simp }
def M8 : Num.Not19 := { suit := M, digit := eight, not1 := by simp, not9 := by simp }
def M9 : Num.Not1  := { suit := M, digit := nine, not1 := by simp }

def P1 : Num.Not9  := { suit := P, digit := one, not9 := by simp }
def P2 : Num.Not19 := { suit := P, digit := two, not1 := by simp, not9 := by simp }
def P3 : Num.Not19 := { suit := P, digit := three, not1 := by simp, not9 := by simp }
def P4 : Num.Not19 := { suit := P, digit := four, not1 := by simp, not9 := by simp }
def P5 : Num.Not19 := { suit := P, digit := five, not1 := by simp, not9 := by simp }
def P6 : Num.Not19 := { suit := P, digit := six, not1 := by simp, not9 := by simp }
def P7 : Num.Not19 := { suit := P, digit := seven, not1 := by simp, not9 := by simp }
def P8 : Num.Not19 := { suit := P, digit := eight, not1 := by simp, not9 := by simp }
def P9 : Num.Not1  := { suit := P, digit := nine, not1 := by simp }

def S1 : Num.Not9  := { suit := S, digit := one, not9 := by simp }
def S2 : Num.Not19 := { suit := S, digit := two, not1 := by simp, not9 := by simp }
def S3 : Num.Not19 := { suit := S, digit := three, not1 := by simp, not9 := by simp }
def S4 : Num.Not19 := { suit := S, digit := four, not1 := by simp, not9 := by simp }
def S5 : Num.Not19 := { suit := S, digit := five, not1 := by simp, not9 := by simp }
def S6 : Num.Not19 := { suit := S, digit := six, not1 := by simp, not9 := by simp }
def S7 : Num.Not19 := { suit := S, digit := seven, not1 := by simp, not9 := by simp }
def S8 : Num.Not19 := { suit := S, digit := eight, not1 := by simp, not9 := by simp }
def S9 : Num.Not1  := { suit := S, digit := nine, not1 := by simp }

end Num

/-- 風牌 -/
inductive Winds : Type
| west -- 西
| east -- 東
| north -- 北
| south -- 南

namespace Winds

def Winds.toString : Winds → String
| west => "西"
| east => "東"
| north => "北"
| south => "南"
instance : ToString Winds where toString := Winds.toString

def West := Winds.west
def East := Winds.east
def North := Winds.north
def South := Winds.south

end Winds

/-- 字牌 -/
inductive Dragons : Type
| red -- 中
| green -- 發
| white -- 白

namespace Dragons

def toString : Dragons → String
| red => "中"
| green => "發"
| white => "白"
instance : ToString Dragons where toString := Dragons.toString

def Red := Dragons.red
def Green := Dragons.green
def White := Dragons.white

end Dragons

open Num.Suit Num.Digit

end Tile

namespace Hand

open Tile Num Winds Dragons

def Dragon3 (d : Dragon) := [d, d, d]

def Wind3 (w : Wind) := [w, w, w]

def Shuntsu (n : Not19) := ([Not1.prev n, n, Not9.next n] : List Num)
def Kotsu (n : Num) := [n, n, n]

abbrev Tile : Type := Num

end Hand
end Mahjong
