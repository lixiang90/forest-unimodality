import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 120
  A := (10183471201233735726532359/100000000000000000000000000)
  B := (94064782774847616186875143/1000000000000000000000000000)
  C := (34049462018265724827514873/50000000000000000000000000)
  dδ := (73709284658344045859657/500000000000000000000000)
  dM := (25962912897035228532161/16000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(33244436883036998509055593/5000000000000000000000000), (1280397625828041396900403/312500000000000000000000), (12194725719193323598688039/500000000000000000000000), (4131710765425201969947011/200000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95549/180624)
  hi := (15929/30104)
  vmin := (225793575/906250816)
  damping := (225793575/906250816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell138
