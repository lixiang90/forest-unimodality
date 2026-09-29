import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-1681192143906350083781831/5000000000000000000000000)
  B := (46668205775964644033138029/500000000000000000000000000)
  C := (11104743951051331690704771/2000000000000000000000000000)
  dδ := (11091541328154069789846403/100000000000000000000000000)
  dM := (18965534838028975245238783/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(13458006131381261560875373/2500000000000000000000000), (20147964372156836887484133/10000000000000000000000000), (8540102410036126912018517/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1531/2926)
  hi := (11/21)
  vmin := (110/441)
  damping := (110/441)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell126
