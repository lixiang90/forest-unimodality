import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 69
  A := (-275830246445864329418729/156250000000000000000000)
  B := (12772139855143890829758391/100000000000000000000000000)
  C := (-26139467255291318030507863/10000000000000000000000000000)
  dδ := (76597529652929485788348529/1000000000000000000000000000)
  dM := (1635444861919922590956511/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11874130232062839240825269/1000000000000000000000000), (2764329130388091471104417/50000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237/19012)
  hi := (4631/9506)
  vmin := (90291675/361456144)
  damping := (90291675/361456144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell049
