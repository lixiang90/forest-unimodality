import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 61
  A := (-2480587624769034721339267/5000000000000000000000000)
  B := (18158825007535198126085163/250000000000000000000000000)
  C := (16718121253418293144232809/5000000000000000000000000000)
  dδ := (39380912648964205846624509/500000000000000000000000000)
  dM := (10603305235176697061960649/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(75796465679925950631457/50000000000000000000000), (36838217845295568864116831/5000000000000000000000000), (1283762406677172585034441/100000000000000000000000), (38707277324569623999650503/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11311/21736)
  hi := (22647/43472)
  vmin := (471623775/1889814784)
  damping := (471623775/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell105
