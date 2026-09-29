import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell215
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 80
  A := (-12206247210969320315854247/10000000000000000000000000)
  B := (2508902169938095200185657/25000000000000000000000000)
  C := (27549110001055582275242273/100000000000000000000000000)
  dδ := (29941062484513572550248739/500000000000000000000000000)
  dM := (11416245603024781796880349/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(8543465520956593506340937/1250000000000000000000000), (7125749232659314813531637/2000000000000000000000000), (12102278555613265709212101/500000000000000000000000)]
  retention := ![(7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97/177)
  hi := (49/89)
  vmin := (1960/7921)
  damping := (1960/7921)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell215
