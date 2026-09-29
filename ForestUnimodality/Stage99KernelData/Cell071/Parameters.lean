import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 63
  A := (-9213637468010708497700989/10000000000000000000000000)
  B := (5617889258104529111303993/62500000000000000000000000)
  C := (15511006872523944513653227/10000000000000000000000000000)
  dδ := (38614683494724556800381521/500000000000000000000000000)
  dM := (12296106671507520818886761/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(83278191074755749667701821/10000000000000000000000000), (48553794285192381607885181/1000000000000000000000000), (25606772971143683115258227/5000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10429/20604)
  hi := (5227/10302)
  vmin := (26527025/106131204)
  damping := (26527025/106131204)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell071
