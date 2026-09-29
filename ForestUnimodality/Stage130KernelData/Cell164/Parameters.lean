import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-652146748590834209210243/400000000000000000000000)
  B := (1123813223428478808019193/10000000000000000000000000)
  C := (12434595843909565602430911/2500000000000000000000000000)
  dδ := (35161374092899239096610131/500000000000000000000000000)
  dM := (6713094814126409045143551/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(16824558856463558420557547/2500000000000000000000000), (16445541275456865282222907/2500000000000000000000000), (30498127082992638747782621/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell164
