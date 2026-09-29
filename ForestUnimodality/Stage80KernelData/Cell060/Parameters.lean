import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (3208756140834034507065553/2000000000000000000000000)
  B := (-527647761232709344714209/200000000000000000000000000)
  C := (-6780666737788599175013049/2500000000000000000000000000)
  dδ := (321078821658529441410157/3125000000000000000000000)
  dM := (32251640053869944351622179/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(59489253146828575680160611/10000000000000000000000000), (5109826132699600620412639/500000000000000000000000), (24335777534099339192152911/1000000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631/9506)
  hi := (9287/19012)
  vmin := (22576125/90364036)
  damping := (22576125/90364036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell060
