import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 108
  A := (32619622217657291308512413/100000000000000000000000000)
  B := (76052844351923568066986547/1000000000000000000000000000)
  C := (11910846592286616907330199/20000000000000000000000000)
  dδ := (13155272891143898750243579/100000000000000000000000000)
  dM := (207490592522588889433377/156250000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(74437976064783129004354123/10000000000000000000000000), (8569100610964131004010369/2500000000000000000000000), (2407936749600641412882851/250000000000000000000000), (3700955183132022874303857/125000000000000000000000)]
  retention := ![(4/5), (3/5), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (32351/60776)
  hi := (48539/91164)
  vmin := (2068974875/8310874896)
  damping := (2068974875/8310874896)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell153
