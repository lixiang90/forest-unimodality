import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-801372399339935948532343/500000000000000000000000)
  B := (24822723897196377618179497/250000000000000000000000000)
  C := (11535285253841845269640043/2500000000000000000000000000)
  dδ := (15737653749194464164462559/250000000000000000000000000)
  dM := (531980223391973795765697/500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(599838484464681354069171/50000000000000000000000), (8542290059582072769828187/5000000000000000000000000), (14947061193633565778782213/1000000000000000000000000), (11537327961116253050022351/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95449/180624)
  hi := (47737/90312)
  vmin := (2032402775/8156257344)
  damping := (2032402775/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell153
