import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-15677380427095745540810867/10000000000000000000000000)
  B := (97457641870584713061909099/1000000000000000000000000000)
  C := (8002240316040418535714629/2000000000000000000000000000)
  dδ := (7772889487728295090929187/125000000000000000000000000)
  dM := (10432759233247859611409813/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(790555201696676257405727/62500000000000000000000), (13053822447957849281485743/1000000000000000000000000000), (73712152911951847045202157/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111/211)
  hi := (23557/44732)
  vmin := (498819475/2000951824)
  damping := (498819475/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell131
