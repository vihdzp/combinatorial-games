import CombinatorialGames.Game.Concrete

inductive Piece : Type where
  | X : Piece
  | O : Piece
  | none : Piece

namespace Piece

def toString : Piece → String
  | .X => "X"
  | .O => "O"
  | .none => "∅"

def toString' : Piece → String
  | .X => "X"
  | .O => "O"
  | .none => " "

instance : ToString Piece where
  toString := toString

instance : Repr Piece where
  reprPrec x _ := toString x

end Piece

def TicTacToe : Type :=
  Fin 9 → Piece

instance : EmptyCollection TicTacToe where
  emptyCollection := fun _ ↦ .none

instance : GetElem TicTacToe ℕ Piece (fun _ n ↦ n < 9) where
  getElem x n hn := x ⟨n, hn⟩

open Std.Format in
instance : Repr TicTacToe where
  reprPrec t _ :=
    t[0].toString' ++ " | " ++ t[1].toString' ++ " | " ++ t[2].toString' ++ line ++
    "——|———|——" ++ line ++
    t[3].toString' ++ " | " ++ t[4].toString' ++ " | " ++ t[5].toString' ++ line ++
    "——|———|——" ++ line ++
    t[6].toString' ++ " | " ++ t[7].toString' ++ " | " ++ t[8].toString' ++ line 

#eval (∅ : TicTacToe)
