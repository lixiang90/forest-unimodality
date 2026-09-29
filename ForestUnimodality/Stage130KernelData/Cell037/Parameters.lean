import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 85
  A := (-13298038440001444426741273/10000000000000000000000000)
  B := (91099054637801366030025463/1000000000000000000000000000)
  C := (-19930045089871077125531773/5000000000000000000000000000)
  dδ := (65257194757478639846048907/1000000000000000000000000000)
  dM := (10101465951850739297124271/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(95721231686670780192116581/10000000000000000000000000), (12204762084885785178300921/10000000000000000000000000), (18204083898297593435700037/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (869/1824)
  hi := (581/1216)
  vmin := (829895/3326976)
  damping := (829895/3326976)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell037
