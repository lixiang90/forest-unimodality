import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-5666168246315154727099639/25000000000000000000000000)
  B := (86873221869665062655485599/1000000000000000000000000000)
  C := (10112783900817132881622129/2000000000000000000000000000)
  dδ := (11099345248886004211552603/100000000000000000000000000)
  dM := (17979196545232847825879219/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(31371605996229976476286083/5000000000000000000000000), (77539456405331552701909459/100000000000000000000000000), (34617710446309629901406879/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4583/8778)
  hi := (2294/4389)
  vmin := (4805930/19263321)
  damping := (4805930/19263321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell122
