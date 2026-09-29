import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 37
  A := (12077780845576803093521789/100000000000000000000000000)
  B := (20185872747490830186878341/1000000000000000000000000000)
  C := (-61457834701000461918862783/1000000000000000000000000000)
  dδ := (20702091918899417216648473/1000000000000000000000000000)
  dM := (120295481457011622572679/781250000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(6422972481903771457822927/2500000000000000000000000), (369817024099824975813533/31250000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97/255)
  hi := (33/85)
  vmin := (15326/65025)
  damping := (15326/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell017
