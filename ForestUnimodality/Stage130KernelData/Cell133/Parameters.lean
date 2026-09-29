import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-17991680016077590720158241/10000000000000000000000000)
  B := (5962218030118888317803183/50000000000000000000000000)
  C := (12737215645499259161071981/2500000000000000000000000000)
  dδ := (34905896958997803536384197/500000000000000000000000000)
  dM := (7064709684720108700053953/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(17382420026280580582778157/5000000000000000000000000), (1477220274003850253308201/125000000000000000000000), (235367515573782128512903/4000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23557/44732)
  hi := (11791/22366)
  vmin := (124689825/500237956)
  damping := (124689825/500237956)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell133
