import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 117
  A := (-17408669861325993155531933/10000000000000000000000000)
  B := (12704558425722450865080759/100000000000000000000000000)
  C := (-10966805466457599238516707/25000000000000000000000000)
  dδ := (84744633689191661840567349/1000000000000000000000000000)
  dM := (14352029596968432674508609/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(65053206106684546838891947/10000000000000000000000000), (46004770385290649770126947/10000000000000000000000000), (20697942979655621797974163/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1613/3478)
  hi := (22/47)
  vmin := (3008245/12096484)
  damping := (3008245/12096484)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell029
