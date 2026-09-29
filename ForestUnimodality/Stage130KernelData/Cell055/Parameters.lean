import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 71
  A := (-3594806056242512906067077/2000000000000000000000000)
  B := (6320851637961732993886699/50000000000000000000000000)
  C := (-2274507865072136585105067/1000000000000000000000000000)
  dδ := (1881295532475522891413533/25000000000000000000000000)
  dM := (790866231748393682353393/500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2488913859693764152325457/200000000000000000000000), (56685060360098326270872349/1000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24/49)
  hi := (9529/19404)
  vmin := (600/2401)
  damping := (600/2401)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell055
