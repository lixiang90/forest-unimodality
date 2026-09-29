import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 24
  A := (3060202085014753187408587/25000000000000000000000000)
  B := (3896861269849376512713901/250000000000000000000000000)
  C := (-3452913783469911939566499/125000000000000000000000000)
  dδ := (962166705881939898423183/62500000000000000000000000)
  dM := (4969199590104553211286631/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(11980420349021159154290217/10000000000000000000000000), (65004056899802389324349861/10000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13/42)
  hi := (20/63)
  vmin := (377/1764)
  damping := (3770000000000000000000000000000000000000000/43524955408804071509263948678105342569819369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell008
