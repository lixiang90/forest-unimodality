import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-6631963699234228191981/4882812500000000000000)
  B := (17753929325109474302024637/200000000000000000000000000)
  C := (-16118963743942400345526833/20000000000000000000000000000)
  dδ := (62713609977217601998411567/1000000000000000000000000000)
  dM := (95065283570208182744448733/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10628713149584834596339533/1000000000000000000000000), (11114029579172060024916391/10000000000000000000000000), (1870994001627618530392283/25000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3193/6468)
  hi := (49/99)
  vmin := (10457075/41835024)
  damping := (10457075/41835024)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell061
