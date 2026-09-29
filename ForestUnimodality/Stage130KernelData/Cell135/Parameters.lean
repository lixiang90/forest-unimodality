import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-18830134233293591050539817/10000000000000000000000000)
  B := (13223940167604375517385051/100000000000000000000000000)
  C := (50847254423606585288508697/10000000000000000000000000000)
  dδ := (4579969204822310728519863/62500000000000000000000000)
  dM := (8449265808079448915324239/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7647024032874939258874747/500000000000000000000000), (5075475372908596227716771/100000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11791/22366)
  hi := (23607/44732)
  vmin := (498697875/2000951824)
  damping := (498697875/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell135
