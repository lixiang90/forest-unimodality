import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 41
  A := (-7102332664884699408958113/20000000000000000000000000)
  B := (4972460057352819096099239/50000000000000000000000000)
  C := (26270598507679696932692881/5000000000000000000000000000)
  dδ := (11465045354081936090917537/100000000000000000000000000)
  dM := (830926341304399733445063/400000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(57800865529299487732828311/10000000000000000000000000), (11178751475382717184281489/50000000000000000000000000), (34531835450472001980415371/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10996/21321)
  hi := (7339/14214)
  vmin := (50455625/202037796)
  damping := (50455625/202037796)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell102
