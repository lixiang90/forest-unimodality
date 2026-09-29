import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 34
  A := (44934279758002782045878121/10000000000000000000000000000)
  B := (79567675555462069603152031/1000000000000000000000000000)
  C := (77290922540661230813463511/10000000000000000000000000000)
  dδ := (11685240460543494522838159/100000000000000000000000000)
  dM := (9673357483272324768355799/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(28969947682228385232861001/5000000000000000000000000), (29532359117251609781362731/5000000000000000000000000), (2774364844466053803273553/125000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4657/8862)
  hi := (111/211)
  vmin := (11100/44521)
  damping := (11100/44521)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell140
