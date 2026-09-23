import SmallCancellation.Words
import SmallCancellation.FiniteCheck
import SmallCancellation.Dehn
import SmallCancellation.Certificates

namespace GreendlingerDehn.Examples

abbrev Atom := Fin 1

def atom : Atom := 0

def sixthPower : FreeGroup Atom := FreeGroup.mk (List.replicate 6 (atom, true))

def symmetrizedRelators : List (FreeGroup Atom) := [sixthPower, sixthPower⁻¹]

/-- The finite C'(1/6) checker accepts the symmetrized one-generator example. -/
example : cPrimeSixCheck symmetrizedRelators = true := by decide

/-- Dehn reduction detects the defining relator as the identity. -/
example : dehnWordProblem symmetrizedRelators sixthPower = true := by decide

/-- A nontrivial power reduces to a shorter free word. -/
example :
    dehnReduce symmetrizedRelators (FreeGroup.mk (List.replicate 4 (atom, true))) =
      FreeGroup.mk (List.replicate 2 (atom, false)) := by decide

end GreendlingerDehn.Examples
