import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-16183154759239645647994621/10000000000000000000000000)
  B := (10007632906586337584453617/100000000000000000000000000)
  C := (47724681578234593587461987/10000000000000000000000000000)
  dδ := (15733711321979027691897457/250000000000000000000000000)
  dM := (67101473286629620992709/62500000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6102402589869966753610697/500000000000000000000000), (94480274468789382513733699/100000000000000000000000000), (18293481055610609331552041/250000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95549/180624)
  hi := (15929/30104)
  vmin := (225793575/906250816)
  damping := (225793575/906250816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell165
