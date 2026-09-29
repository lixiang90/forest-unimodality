import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 61
  A := (-57425887254527501312395543/100000000000000000000000000)
  B := (15128410299040737085896069/200000000000000000000000000)
  C := (28108467247138680007723099/10000000000000000000000000000)
  dδ := (78255371922675065476937561/1000000000000000000000000000)
  dM := (2724920428677353955414231/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5810235398575908094542797/5000000000000000000000000), (38440490651936261023990937/5000000000000000000000000), (16419094270055680784281549/5000000000000000000000000), (48216342538143194929034507/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22331/43056)
  hi := (27/52)
  vmin := (675/2704)
  damping := (675/2704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell099
