import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 116
  A := (2910876177910899892609109/25000000000000000000000000)
  B := (712190042752416647801883/7812500000000000000000000)
  C := (65701130051744038862437947/100000000000000000000000000)
  dδ := (14365881834775945380400231/100000000000000000000000000)
  dM := (7826515097433773757162889/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(62665974409541798095801823/10000000000000000000000000), (8471246567491871104493839/2000000000000000000000000), (21000493577882753726271403/1000000000000000000000000), (22321320879012276350294997/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95749/180624)
  hi := (47887/90312)
  vmin := (2031605975/8156257344)
  damping := (2031605975/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell146
