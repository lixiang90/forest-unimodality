import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell201
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 5) where
  terms := Finset.univ
  scale := 48
  A := (77606007054481272555790383/10000000000000000000000000)
  B := (-11978903812409369411540183/100000000000000000000000000)
  C := (18529585971114315157137753/50000000000000000000000000)
  dδ := (1394152002200611112359141/12500000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(2060993312709874236698937/312500000000000000000000), (18964441608812461215194389/10000000000000000000000000), (1593207849206883519599387/500000000000000000000000), (20979837901732754090744493/10000000000000000000000000), (2920782770214443857526021/200000000000000000000000)]
  retention := ![(19/20), (9/10), (7/10), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (116/207)
  hi := (13/23)
  vmin := (130/529)
  damping := (130/529)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell201
