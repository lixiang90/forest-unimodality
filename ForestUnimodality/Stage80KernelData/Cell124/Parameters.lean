import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-30416767855084596682502251/100000000000000000000000000)
  B := (45674097919379250121174607/500000000000000000000000000)
  C := (53035278215698587397919361/10000000000000000000000000000)
  dδ := (5537132429210644274375497/50000000000000000000000000)
  dM := (18646816946815373151197237/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(28428430264084729728324419/5000000000000000000000000), (3117064875038870752632647/2000000000000000000000000), (3434618471035003040014999/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2294/4389)
  hi := (1531/2926)
  vmin := (2135745/8561476)
  damping := (2135745/8561476)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell124
