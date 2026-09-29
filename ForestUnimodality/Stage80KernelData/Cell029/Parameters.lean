import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 92
  A := (32846256643725186719962039/100000000000000000000000000)
  B := (1932688268047045021535979/20000000000000000000000000)
  C := (-17656715304090672691295083/25000000000000000000000000)
  dδ := (864443616443136553240123/5000000000000000000000000)
  dM := (5372837174724208290921279/2500000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(46018416479892945147867067/5000000000000000000000000), (12976318762115498728348939/2000000000000000000000000), (6705325585295676127373099/250000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1613/3478)
  hi := (22/47)
  vmin := (3008245/12096484)
  damping := (3008245/12096484)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell029
