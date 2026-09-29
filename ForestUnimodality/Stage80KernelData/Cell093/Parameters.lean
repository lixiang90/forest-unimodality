import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (-59188507263073498734229361/1000000000000000000000000000)
  B := (10479817022349777189127451/125000000000000000000000000)
  C := (4924955333065268898995459/2000000000000000000000000000)
  dδ := (2365257343712308391037169/20000000000000000000000000)
  dM := (19075672840811594074827973/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(733466017114517421227049/125000000000000000000000), (32957292966301714898236241/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5227/10302)
  hi := (3493/6868)
  vmin := (11788875/47169424)
  damping := (11788875/47169424)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell093
