import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 55
  A := (5797985186905377730681721/50000000000000000000000000)
  B := (26816813835421882822318551/500000000000000000000000000)
  C := (-10869380223262463738831407/2000000000000000000000000000)
  dδ := (44793185849598279868466477/500000000000000000000000000)
  dM := (48832681291814227907827073/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7042148942291651669833641/5000000000000000000000000), (8233408283341936417798479/1250000000000000000000000), (11759165401757048385888993/250000000000000000000000)]
  retention := ![(4/5), (7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1677/3572)
  hi := (841/1786)
  vmin := (3177915/12759184)
  damping := (3177915/12759184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell031
