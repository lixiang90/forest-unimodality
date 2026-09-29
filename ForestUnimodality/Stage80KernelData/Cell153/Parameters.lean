import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (51993035271676541975161/312500000000000000000000)
  B := (8570979740908825014744643/125000000000000000000000000)
  C := (35900295597435360334115373/5000000000000000000000000000)
  dδ := (18670257232341748269977/156250000000000000000000)
  dM := (8245476516213568266011613/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(18148882586706716057989297/2500000000000000000000000), (6870915093698114262110721/250000000000000000000000), (10777161790552349796001863/2500000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31833/60208)
  hi := (23881/45156)
  vmin := (508068275/2039064336)
  damping := (508068275/2039064336)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell153
