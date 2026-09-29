import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 37
  A := (-40754624792332206908440639/1000000000000000000000000000)
  B := (2048759841900103448320003/25000000000000000000000000)
  C := (50003368598222058122315659/10000000000000000000000000000)
  dδ := (2324363171409567774272631/20000000000000000000000000)
  dM := (19098838162365976492407249/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(62359557911027412302473749/10000000000000000000000000), (43513783850523148899469561/10000000000000000000000000), (13130351688670977239326021/500000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11/21)
  hi := (1549/2954)
  vmin := (2176345/8726116)
  damping := (2176345/8726116)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell129
