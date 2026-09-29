import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell227
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 19
  A := (36890357786871376012172163/100000000000000000000000000)
  B := (8728380771333848348048079/250000000000000000000000000)
  C := (11537299530308645079124119/100000000000000000000000000)
  dδ := (3646576572584731262133273/62500000000000000000000000)
  dM := (65220659912736535061827947/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(6980909643118560659047489/1000000000000000000000000)]
  retention := ![(3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9/14)
  hi := (41/63)
  vmin := (902/3969)
  damping := (902/3969)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell227
