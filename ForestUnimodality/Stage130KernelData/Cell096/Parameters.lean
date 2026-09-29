import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 90
  A := (-15821034481403117199960207/10000000000000000000000000)
  B := (48488925265680229981235527/500000000000000000000000000)
  C := (26930418150288406090031579/10000000000000000000000000000)
  dδ := (7649159758404536213483027/125000000000000000000000000)
  dM := (10269662181602917314093837/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1542852446682775324759973/125000000000000000000000), (76016586742145250354951713/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7339/14214)
  hi := (107/207)
  vmin := (10700/42849)
  damping := (10700/42849)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell096
