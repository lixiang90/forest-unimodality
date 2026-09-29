import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 18
  A := (45604987747434221354581041/1000000000000000000000000000)
  B := (14910375289234467990895361/500000000000000000000000000)
  C := (-43210389056195938617399577/1000000000000000000000000000)
  dδ := (1659101036199653583097513/62500000000000000000000000)
  dM := (15698682824672713408478697/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(12611264878725247928770159/100000000000000000000000000), (27105874523765516315165769/5000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19/63)
  hi := (13/42)
  vmin := (836/3969)
  damping := (33440000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell007
