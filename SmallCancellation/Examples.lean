import SmallCancellation.Words
import SmallCancellation.FiniteCheck
import SmallCancellation.Dehn
import SmallCancellation.CyclicDehn
import SmallCancellation.Certificates

namespace GreendlingerDehn.Examples

abbrev Atom := Fin 1

def atom : Atom := 0

def sixthPower : FreeGroup Atom := FreeGroup.mk (List.replicate 6 (atom, true))

def symmetrizedRelators : List (FreeGroup Atom) := [sixthPower, sixthPower⁻¹]

abbrev DistinctAtom := Fin 8

def longRelator : FreeGroup DistinctAtom :=
  FreeGroup.mk ([(0, true), (1, true), (2, true), (3, true),
    (4, true), (5, true), (6, true), (7, true)] : Word DistinctAtom)

def cyclicOrbit (r : FreeGroup DistinctAtom) : List (FreeGroup DistinctAtom) :=
  (cyclicShifts r.toWord).map fun p => FreeGroup.mk p.2

def cPrimeSymmetrizedRelators : List (FreeGroup DistinctAtom) :=
  cyclicOrbit longRelator ++ cyclicOrbit longRelator⁻¹

/-- The finite checker accepts a symmetrized relator with distinct cyclic
letters; the periodic one-generator relator below is intentionally excluded. -/
example : cPrimeSixCheck cPrimeSymmetrizedRelators = true := by decide

/-- Repeated cyclic positions in a proper-power relator are pieces, so the
one-generator periodic presentation fails the strict C'(1/6) test. -/
example : cPrimeSixCheck symmetrizedRelators = false := by decide

/-- Dehn reduction detects the defining relator as the identity. -/
example : dehnWordProblem symmetrizedRelators sixthPower = true := by decide

/-- The cyclic Dehn reducer detects a defining relator. -/
example : cyclicDehnWordProblem symmetrizedRelators sixthPower = true := by decide

/-- A nontrivial power reduces to a shorter free word. -/
example :
    dehnReduce symmetrizedRelators (FreeGroup.mk (List.replicate 4 (atom, true))) =
      FreeGroup.mk (List.replicate 2 (atom, false)) := by decide

end GreendlingerDehn.Examples
