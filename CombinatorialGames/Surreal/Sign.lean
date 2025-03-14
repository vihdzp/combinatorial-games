import CombinatorialGames.Surreal.Basic

inductive Sign : Type
  | plus : Sign
  | zero : Sign
  | minus : Sign

namespace Sign

notation " ＋ " => plus
notation " ０ " => zero
notation " － " => minus

/-- Turns a sign into an integer in the obvious way. -/
def toInt : Sign → ℤ
  | plus => 1
  | zero => 0
  | minus => -1

@[simp] theorem toInt_plus : toInt ＋ = 1 := rfl
@[simp] theorem toInt_zero : toInt ０ = 0 := rfl
@[simp] theorem toInt_minus : toInt － = -1 := rfl



end Sign
