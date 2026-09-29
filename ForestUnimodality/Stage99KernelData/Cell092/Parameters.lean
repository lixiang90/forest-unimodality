import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 49
  A := (-960202921861095550752907/2000000000000000000000000)
  B := (85604043528267920182273087/1000000000000000000000000000)
  C := (37089188201078300208268779/10000000000000000000000000000)
  dδ := (93656852696424666704366757/1000000000000000000000000000)
  dM := (3693527970849694091678983/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(73346428985462726046762327/10000000000000000000000000), (2568457356665428736874901/62500000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/207)
  hi := (7427/14352)
  vmin := (51431975/205979904)
  damping := (51431975/205979904)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell092
