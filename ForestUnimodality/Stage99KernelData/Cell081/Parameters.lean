import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 62
  A := (-48914417075471519124718611/50000000000000000000000000)
  B := (93511424066469964189174391/1000000000000000000000000000)
  C := (12752526136586763306351999/5000000000000000000000000000)
  dδ := (15470018460657536385483013/200000000000000000000000000)
  dM := (12895729492463738931340433/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1285102669405121245116419/156250000000000000000000), (3085934442317201487071543/125000000000000000000000), (28034789448684193757799221/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5381/10506)
  hi := (10787/21012)
  vmin := (110297075/441504144)
  damping := (110297075/441504144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell081
