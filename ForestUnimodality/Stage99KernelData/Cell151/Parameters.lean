import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 110
  A := (80179534803996265210912497/1000000000000000000000000000)
  B := (87014411886411846541733439/1000000000000000000000000000)
  C := (60761204834419502152087489/100000000000000000000000000)
  dδ := (1335870172083266360640863/10000000000000000000000000)
  dM := (3635781183330529181887969/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(29350491092787311941947337/5000000000000000000000000), (4048125027911921414158769/1000000000000000000000000), (10344860419419489971915027/500000000000000000000000), (5063394301876818381913381/250000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (12116/22791)
  hi := (24257/45582)
  vmin := (517280525/2077718724)
  damping := (517280525/2077718724)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell151
