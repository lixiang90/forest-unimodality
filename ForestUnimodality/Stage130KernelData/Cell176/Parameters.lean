import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell176
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-16009384053720476137527839/10000000000000000000000000)
  B := (11127528588116743224478711/100000000000000000000000000)
  C := (1967807427868232747480981/400000000000000000000000000)
  dδ := (35233379466782191458129603/500000000000000000000000000)
  dM := (6661327086945312801746777/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(72526095574119473496921273/10000000000000000000000000), (29541148757844895023083609/5000000000000000000000000), (61172685045333793141253409/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31883/60208)
  hi := (47837/90312)
  vmin := (2031876575/8156257344)
  damping := (2031876575/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell176
