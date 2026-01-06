import Cslib.Foundations.Semantics.LTS.Basic

namespace Cslib

universe u v

structure ReachabilityGame where
  Label : Type v
  Pos : Type u
  Moves : LTS Pos Label
  Defender : Pos → Prop
  decDefender : DecidablePred Defender
  initial : Pos

namespace ReachabilityGame

variable {G : ReachabilityGame}

def Attacker : Set G.Pos := { p : G.Pos | ¬G.Defender p }

def step (p p' : G.Pos) : Prop := ∃ (l : G.Label), G.Moves.Tr p l p'

structure Play where
  path : List G.Pos
  not_empty : path ≠ []
  start_eq_initial : (path.head? : Option G.Pos) = some G.initial
  is_path : List.IsChain step path

def InfinitePlay (G : ReachabilityGame) := Nat → G.Pos

def isInfinitePlay (G : ReachabilityGame) (π : InfinitePlay G) : Prop :=
π 0 = G.initial ∧ ∀ n, step (π n) (π (n + 1))

inductive Winner where
  | defender
  | attacker



def winnerFinite (p : @Play G) : Winner :=
  let lastNode := p.path.getLast p.not_empty

  have h : Decidable (lastNode ∈ G.Attacker) := by
    unfold Attacker
    simp only [Set.mem_setOf]

    exact @instDecidableNot (G.Defender lastNode) (G.decDefender lastNode)

  if h : lastNode ∈ G.Attacker then
    Winner.defender
  else
    Winner.attacker

def winnerInfinite (π : InfinitePlay G) : Winner :=
  Winner.defender

end ReachabilityGame

end Cslib
