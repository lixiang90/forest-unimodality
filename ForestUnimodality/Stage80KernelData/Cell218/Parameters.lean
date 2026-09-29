import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell218
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 32
  A := (31600121068582898809040671/10000000000000000000000000)
  B := (-52142240191619927680566349/1000000000000000000000000000)
  C := (5678482076497284869454063/25000000000000000000000000)
  dδ := (81319090386396133962598753/1000000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(10330899764387222461436977/2500000000000000000000000), (7734856140611260366668489/10000000000000000000000000), (95223210381366154564375393/10000000000000000000000000), (98684545688432642740473/62500000000000000000000)]
  retention := ![(9/10), (7/10), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/90)
  hi := (107/180)
  vmin := (7811/32400)
  damping := (7811/32400)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell218
