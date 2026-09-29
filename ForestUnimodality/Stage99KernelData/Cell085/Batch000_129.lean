import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell085.Parameters
import ForestUnimodality.BinomialMassData.Q53_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_103.Batch100_149
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch000_049
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch050_099
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree000.table
  base := (60924624340486792363194013/1000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (780424069713369084055898380000000000000)
      linear := (-26567474530565134138715422000000000000)
      constant := (609246243404867923631940130000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree000.table
  base := (60924624340486792363194013/1000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (780424069713369084055898380000000000000)
      linear := (-26567474530565134138715422000000000000)
      constant := (609246243404867923631940130000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree001.table
  base := (172154523735425872493714041622555817917081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-8802524330425329167799930424838000000000000)
      constant := (3655111927673553371396000801185507344564624658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree001.table
  base := (344008299852676344769832429806307170752787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-377595350574153898067088114007882962000000000000)
      constant := (156481396873862209112099870249753287607249679259267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24988522174567113069/50000000000000000000)
  directionHi := (49977044349134226139/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree002.table
  base := (12733477329772303947087495777995862798937/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-17323194323555892827522228937678000000000000)
      constant := (2170490284399094086357398452515205734942762128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree002.table
  base := (50854408359013546175282173871707007364609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-743113524649564388878557778218563622000000000000)
      constant := (92859649259574669732251049044576063305312336855876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24988522174567113069/50000000000000000000)
  centralHi := (49977044349134226139/100000000000000000000)
  directionLo := (17669553481466818341/25000000000000000000)
  directionHi := (14135642785173454673/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree003.table
  base := (127526829185818867655529235188753076941079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-25843864316686456487244527450518000000000000)
      constant := (1373097127269163115973316565528355393267907111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree003.table
  base := (63634871609874744803261613648820631365121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-123181299858330542187780826936582698000000000000)
      constant := (6524546685377688750220524575604388594168759056658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669553481466818341/25000000000000000000)
  centralHi := (14135642785173454673/20000000000000000000)
  directionLo := (86562780024823531863/100000000000000000000)
  directionHi := (10820347503102941483/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree004.table
  base := (84881089142354096933189622625432007191163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-34364534309817020146966825963358000000000000)
      constant := (936158981474281694747069993178720164291048267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree004.table
  base := (8469107310159307293904446992453917608963/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-1474149872800385370501497106639924942000000000000)
      constant := (40030552833815416315909173759000717056810673224830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/100000000000000000000)
  centralHi := (10820347503102941483/12500000000000000000)
  directionLo := (99954088698268452277/100000000000000000000)
  directionHi := (49977044349134226139/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree005.table
  base := (7493289355960506672240067991964542619521/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-42885204302947583806689124476198000000000000)
      constant := (691500893732013241550500751793004661203986312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree005.table
  base := (59809428208980248621987330403340875041007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-1839668046875795861312966770850605602000000000000)
      constant := (29573284898900331427053292950228738977492043776287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99954088698268452277/100000000000000000000)
  centralHi := (49977044349134226139/50000000000000000000)
  directionLo := (55876034239592931283/50000000000000000000)
  directionHi := (111752068479185862567/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree006.table
  base := (1781048293818711120694919169036628486959/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-51405874296078147466411422989038000000000000)
      constant := (552168328414536522645958089319047790453700775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree006.table
  base := (11106677457284335746955560791345024571569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-245020691216800705791604048340142918000000000000)
      constant := (2624709258242852935282503424597691378005645021924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55876034239592931283/50000000000000000000)
  centralHi := (111752068479185862567/100000000000000000000)
  directionLo := (24483651501564856011/20000000000000000000)
  directionHi := (15302282188478035007/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree007.table
  base := (6871407222368729483401750380479163033821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-59926544289208711126133721501878000000000000)
      constant := (472927368394203575016426490274983203129034945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree007.table
  base := (1714127145875868454557544352741743717599/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-2570704395026616842935906099271966922000000000000)
      constant := (20241145345370682400376526788501669039524676731180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24483651501564856011/20000000000000000000)
  centralHi := (15302282188478035007/12500000000000000000)
  directionLo := (2066044228278985427/1562500000000000000)
  directionHi := (132226830609855067329/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree008.table
  base := (3399636036094132620961787846761187846859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-68447214282339274785856020014718000000000000)
      constant := (429995681959870704799608025202779534938617048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree008.table
  base := (13569538405774205215820980301983299474691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-2936222569102027333747375763482647582000000000000)
      constant := (18412277527258217547803599660300765282035373394662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2066044228278985427/1562500000000000000)
  centralHi := (132226830609855067329/100000000000000000000)
  directionLo := (17669553481466818341/12500000000000000000)
  directionHi := (141356427851734546729/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree009.table
  base := (10924366166827570423836155731231464949599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-76967884275469838445578318527558000000000000)
      constant := (410667596076721739184479282206571223300591582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree009.table
  base := (21801724839479471423981016461601425285189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-40762231397252318821714141082633682000000000000)
      constant := (217194304181386444319540276416676624529951583429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669553481466818341/12500000000000000000)
  centralHi := (141356427851734546729/100000000000000000000)
  directionLo := (9370695815462667401/6250000000000000000)
  directionHi := (149931133047402678417/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree010.table
  base := (1103548639130979327705532464653107656841/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-85488554268600402105300617040398000000000000)
      constant := (407992199817757881385982232509057106102818704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree010.table
  base := (17617382398672438413868624929989111433677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-3667258917252848315370315091904008902000000000000)
      constant := (17485637097105400122911648901423381620631627825757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9370695815462667401/6250000000000000000)
  centralHi := (149931133047402678417/100000000000000000000)
  directionLo := (158041290866511505003/100000000000000000000)
  directionHi := (39510322716627876251/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree011.table
  base := (890659144497851338577127982489010750829/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-94009224261730965765022915553238000000000000)
      constant := (418036952732536487966006979115112640888717776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree011.table
  base := (1421669418885289343384812398058353402851/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-4032777091328258806181784756114689562000000000000)
      constant := (17923069508178698343902835821348707722275113518910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158041290866511505003/100000000000000000000)
  centralHi := (39510322716627876251/25000000000000000000)
  directionLo := (16575510423702982347/10000000000000000000)
  directionHi := (165755104237029823471/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree012.table
  base := (2852695466450572427215443026955299161557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-102529894254861529424745214066078000000000000)
      constant := (438475781438623693352748181272731075219832852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree012.table
  base := (2845301764929704161153831009957116100117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-488699473933741032999250491147263358000000000000)
      constant := (2089525593069508200202601635639994907383754022132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16575510423702982347/10000000000000000000)
  centralHi := (165755104237029823471/100000000000000000000)
  directionLo := (86562780024823531863/50000000000000000000)
  directionHi := (173125560049647063727/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree013.table
  base := (9000604033626299377006956328802435362717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-111050564247992093084467512578918000000000000)
      constant := (467856516956152310917189151897319036763064653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree013.table
  base := (560906842398094232771167693339097095207/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-4763813439479079787804724084536050882000000000000)
      constant := (20071608943169488791944880877994083374842479975792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/50000000000000000000)
  centralHi := (173125560049647063727/100000000000000000000)
  directionLo := (180194795996941267681/100000000000000000000)
  directionHi := (90097397998470633841/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree014.table
  base := (6929364942691000136897740723678350599121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-119571234241122656744189811091758000000000000)
      constant := (505217476003153127788185231865595621506074689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree014.table
  base := (3453111111659875264344791532658236175613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-5129331613554490278616193748746731542000000000000)
      constant := (21679620282706038252403747527472778719757437610266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180194795996941267681/100000000000000000000)
  centralHi := (90097397998470633841/50000000000000000000)
  directionLo := (186996977158066942889/100000000000000000000)
  directionHi := (18699697715806694289/10000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree015.table
  base := (5133477595732688110486556802980800208487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-128091904234253220403912109604598000000000000)
      constant := (549884064125655509523529767072793309411838583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree015.table
  base := (5112910317813173618016525681475084999573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-610538865292211196603073712550823578000000000000)
      constant := (2622325307191732558366089922287382220556597465277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186996977158066942889/100000000000000000000)
  centralHi := (18699697715806694289/10000000000000000000)
  directionLo := (12097516278554146889/6250000000000000000)
  directionHi := (7742410418274654009/4000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree016.table
  base := (713207597420476498541483067651955621701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-136612574227383784063634408117438000000000000)
      constant := (601358676727729418762277677794285985953129545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree016.table
  base := (3547756153408771657624209862705198315299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-5860367961705311260239133077168092862000000000000)
      constant := (25814248804775476754464384033741321459073326842259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097516278554146889/6250000000000000000)
  centralHi := (7742410418274654009/4000000000000000000)
  directionLo := (39981635479307380911/20000000000000000000)
  directionHi := (49977044349134226139/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree017.table
  base := (2191041706146045653701693386903680970571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-145133244220514347723356706630278000000000000)
      constant := (659259343016746170289258833231907151416787739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree017.table
  base := (1087402943702721719639461922188205594059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-6225886135780721751050602741378773522000000000000)
      constant := (28303239323797301796422400326830729903383479742838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39981635479307380911/20000000000000000000)
  centralHi := (49977044349134226139/25000000000000000000)
  directionLo := (51515158176914660091/25000000000000000000)
  directionHi := (41212126541531728073/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree018.table
  base := (196006179733166416904933104020189414167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-153653914213644911383079005143118000000000000)
      constant := (723284153617520821100078641311394947474488515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree018.table
  base := (965633243244511164853056509363150719651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-81375361850075706689655214883820422000000000000)
      constant := (383394779774026719325941090826470135305947275811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51515158176914660091/25000000000000000000)
  centralHi := (41212126541531728073/20000000000000000000)
  directionLo := (212034641777601820093/100000000000000000000)
  directionHi := (106017320888800910047/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree019.table
  base := (-3597956196084936528252052728263723027/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-162174584206775475042801303655958000000000000)
      constant := (793189584562450325305095747941028254060163925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree019.table
  base := (-25673611669861024238345133189711185269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-6956922483931542732673542069800134842000000000000)
      constant := (34059037470828415424693686718320837638265332155884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212034641777601820093/100000000000000000000)
  centralHi := (106017320888800910047/50000000000000000000)
  directionLo := (10892244290736328369/5000000000000000000)
  directionHi := (217844885814726567381/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree020.table
  base := (-207533315207456586455366022431085934663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-170695254199906038702523602168798000000000000)
      constant := (868776516894009069561947478882103046595801165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree020.table
  base := (-209785832710396641778910476621783782907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-7322440658006953223485011734010815502000000000000)
      constant := (37306895881057985860896677895547893927770431529065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10892244290736328369/5000000000000000000)
  centralHi := (217844885814726567381/100000000000000000000)
  directionLo := (223504136958371725133/100000000000000000000)
  directionHi := (111752068479185862567/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree021.table
  base := (-375721240834831388352564905916273036849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-179215924193036602362245900681638000000000000)
      constant := (949880679907386332304207572122549296760344795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree021.table
  base := (-944270282482292500672021204986328797687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-854217648009151523810720155357944018000000000000)
      constant := (4532391124161599689850466049759580967791994311074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223504136958371725133/100000000000000000000)
  centralHi := (111752068479185862567/50000000000000000000)
  directionLo := (229023588740072613047/100000000000000000000)
  directionHi := (28627948592509076631/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree022.table
  base := (-328202067491181551184900048173754469361/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-187736594186167166021968199194478000000000000)
      constant := (1036365761207289469310327585782033110676393208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree022.table
  base := (-2634364268849474397136874513781231722461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-8053477006157774205107951062432176822000000000000)
      constant := (44507075300113668666198055199172358226414565694099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229023588740072613047/100000000000000000000)
  centralHi := (28627948592509076631/12500000000000000000)
  directionLo := (46882623288914729531/20000000000000000000)
  directionHi := (29301639555571705957/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree023.table
  base := (-1644700132499367878428351001550586779167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-196257264179297729681690497707318000000000000)
      constant := (1128118216043610216415348753332333649719634594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree023.table
  base := (-1648545315710481774201486751062372301953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (104838138)
      previous := (52419069)
      next := (52419069)
      square := (670641035402719741632671098987020000000000000)
      linear := (-15914924726338723432739925759249258000000000000)
      constant := (91585447548237830886702230706183399344270060926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46882623288914729531/20000000000000000000)
  centralHi := (29301639555571705957/12500000000000000000)
  directionLo := (119840742365787868937/50000000000000000000)
  directionHi := (1917451877852605903/800000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree024.table
  base := (-3878895113325187825878677002125303103407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-204777934172428293341412796220158000000000000)
      constant := (1225043223996945368066669739879124659375955137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree024.table
  base := (-1942822850720798044574744055086615930107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-976057039367621687414543376761504238000000000000)
      constant := (5845815758658237770014115586551315556191345837914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119840742365787868937/50000000000000000000)
  centralHi := (1917451877852605903/800000000000000000)
  directionLo := (24483651501564856011/10000000000000000000)
  directionHi := (244836515015648560111/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree025.table
  base := (-2200788951243371314089152159863344961317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-213298604165558857001135094732998000000000000)
      constant := (1327061463509610622334874150076969546610775894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree025.table
  base := (-550936903565499012788869706541767788811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-9150031528384005677542360055064218802000000000000)
      constant := (56994601706738902204864514950788801472086977789992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24483651501564856011/10000000000000000000)
  centralHi := (244836515015648560111/100000000000000000000)
  directionLo := (124942610872835565347/50000000000000000000)
  directionHi := (49977044349134226139/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree026.table
  base := (-4863711043597835134778321667678136280631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-221819274158689420660857393245838000000000000)
      constant := (1434106496662092938612381759541670652198785721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree026.table
  base := (-4868891201732158916805779764814624099283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-9515549702459416168353829719274899462000000000000)
      constant := (61592639328757106040037233783942373128427849374397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124942610872835565347/50000000000000000000)
  centralHi := (49977044349134226139/20000000000000000000)
  directionLo := (127416962183963718739/50000000000000000000)
  directionHi := (254833924367927437479/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree027.table
  base := (-2635272293731546453530412511046942834313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-230339944151819984320579691758678000000000000)
      constant := (1546122625665406023100489912062631966941546766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree027.table
  base := (-329692120775133956165253642550094828037/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-121988492302899094557596288685007162000000000000)
      constant := (819803364528829652490624399024679730156624672688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127416962183963718739/50000000000000000000)
  centralHi := (254833924367927437479/100000000000000000000)
  directionLo := (259688340074470595589/100000000000000000000)
  directionHi := (25968834007447059559/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree028.table
  base := (-5626483011920843445731482318736005586417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-238860614144950547980301990271518000000000000)
      constant := (1663063123414163059344212176509353716733702047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree028.table
  base := (-1126087773517560051942557472263703251003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-10246586050610237149976769047696260782000000000000)
      constant := (71426903196493999630187837833903139750154839769385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259688340074470595589/100000000000000000000)
  centralHi := (25968834007447059559/10000000000000000000)
  directionLo := (2066044228278985427/781250000000000000)
  directionHi := (264453661219710134657/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree029.table
  base := (-92737868016197353187451289959480705953/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-247381284138081111640024288784358000000000000)
      constant := (1784888765930944692604879850182933628194855872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree029.table
  base := (-2969337465484985707250349862387774431333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-10612104224685647640788238711906941442000000000000)
      constant := (76659454408210798119142151565818199492467473020694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2066044228278985427/781250000000000000)
  centralHi := (264453661219710134657/100000000000000000000)
  directionLo := (269134620393557969457/100000000000000000000)
  directionHi := (134567310196778984729/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree030.table
  base := (-3099935648751643822880133454411303085597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-255901954131211675299746587297198000000000000)
      constant := (1911566611351026654785743447503240971129802854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree030.table
  base := (-3101439804365818997449707083222246446863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-1219735822084562014622189819568624678000000000000)
      constant := (9122257565678012206866870608793244464853484183026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269134620393557969457/100000000000000000000)
  centralHi := (134567310196778984729/50000000000000000000)
  directionLo := (273735545474569083329/100000000000000000000)
  directionHi := (27373554547456908333/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree031.table
  base := (-642303514797976247443655245040907398627/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-264422624124342238959468885810038000000000000)
      constant := (2043068981826100167579474113195868134079661570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree031.table
  base := (-6425654894733712540715449132395902456239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-11343140572836468622411178040328302762000000000000)
      constant := (87748311417681990182961529253991902695698593479201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273735545474569083329/100000000000000000000)
  centralHi := (27373554547456908333/10000000000000000000)
  directionLo := (278260406486685072263/100000000000000000000)
  directionHi := (34782550810835634033/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree032.table
  base := (-3303453981869631449843188654293030837591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-272943294117472802619191184322878000000000000)
      constant := (2179372613312135769333382137377626471687994162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree032.table
  base := (-6609187400667403339333787757224771403499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-11708658746911879113222647704538983422000000000000)
      constant := (93602440386985140083960790549352133229324779541541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278260406486685072263/100000000000000000000)
  centralHi := (34782550810835634033/12500000000000000000)
  directionLo := (282712855703469093457/100000000000000000000)
  directionHi := (141356427851734546729/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree033.table
  base := (-844166695391246566236018321244798308093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-281463964110603366278913482835718000000000000)
      constant := (2320457944740277580146181020484725477995530904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree033.table
  base := (-1688828830219420333999399413163809295963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-1341575213443032178226013040972184898000000000000)
      constant := (11073541042595542775501382806830489186879323782452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282712855703469093457/100000000000000000000)
  centralHi := (141356427851734546729/50000000000000000000)
  directionLo := (17943516384525683757/6250000000000000000)
  directionHi := (287096262152410940113/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree034.table
  base := (-857982849007275611055609010860377270711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-289984634103733929938635781348558000000000000)
      constant := (2466308523186305519848088209775510060280216008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree034.table
  base := (-6865584458813212076802927950341912534527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-12439695095062700094845587032960344742000000000000)
      constant := (105925895707682135300949133505907484524473629789393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17943516384525683757/6250000000000000000)
  centralHi := (287096262152410940113/100000000000000000000)
  directionLo := (145706870723175916143/50000000000000000000)
  directionHi := (291413741446351832287/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree035.table
  base := (-6939800477291574049039593678893483106767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-298505304096864493598358079861398000000000000)
      constant := (2616910505743041970731400335804549037720308897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree035.table
  base := (-1735323784027416450315280249450247097837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-12805213269138110585657056697171025402000000000000)
      constant := (112393928253187826705380111901640694852278545374732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145706870723175916143/50000000000000000000)
  centralHi := (291413741446351832287/100000000000000000000)
  directionLo := (295668181692985904191/100000000000000000000)
  directionHi := (4619815338952904753/1562500000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree036.table
  base := (-6982244771111427729058408307187443104203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-307025974089995057258080378374238000000000000)
      constant := (2772252242112934114862368295910496416107510373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree036.table
  base := (-3491770746265227374840289385284488134981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-162601622755722482425537362486193902000000000000)
      constant := (1469944069633428996410430662765188735567793792118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295668181692985904191/100000000000000000000)
  centralHi := (4619815338952904753/1562500000000000000)
  directionLo := (299862266094805356833/100000000000000000000)
  directionHi := (149931133047402678417/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree037.table
  base := (-6992120138490105209651918203348773448127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-315546644083125620917802676887078000000000000)
      constant := (2932323924647090404807265351018478862488820657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree037.table
  base := (-6993244429187619807283727643508571315961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-13536249617288931567279996025592386722000000000000)
      constant := (125940101241172127261140935865189823068482444860599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299862266094805356833/100000000000000000000)
  centralHi := (149931133047402678417/50000000000000000000)
  directionLo := (303998492741966047321/100000000000000000000)
  directionHi := (151999246370983023661/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree038.table
  base := (-435637814241417844274138060347783647387/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-324067314076256184577524975399918000000000000)
      constant := (3097117294786063087268732899017329812557941072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree038.table
  base := (-6971179236991097136934110992105998017023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-13901767791364342058091465689803067382000000000000)
      constant := (133017470620130882103165561902518617561085680847057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303998492741966047321/100000000000000000000)
  centralHi := (151999246370983023661/50000000000000000000)
  directionLo := (61615838402560915843/20000000000000000000)
  directionHi := (19254949500800286201/6250000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree039.table
  base := (-1383431018592778155722518925667626002173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-332587984069386748237247273912758000000000000)
      constant := (3266625396699380494921866849315002778714733215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree039.table
  base := (-3458999389191434542292217383573616488939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-1585253996159972505433659483779305338000000000000)
      constant := (15588586777298228592273619419696409322412753030778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61615838402560915843/20000000000000000000)
  centralHi := (19254949500800286201/6250000000000000000)
  directionLo := (312106541926211220073/100000000000000000000)
  directionHi := (156053270963105610037/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree040.table
  base := (-6833522689350502797176832694095976605257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-341108654062517311896969572425598000000000000)
      constant := (3440842370446940729896110560568255784194828487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree040.table
  base := (-5467402357068764438314735941276062567/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-14632804139515163039714405018224428702000000000000)
      constant := (147779282394711967080960969018753942462077174691250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312106541926211220073/100000000000000000000)
  centralHi := (156053270963105610037/50000000000000000000)
  directionLo := (158041290866511505003/50000000000000000000)
  directionHi := (316082581733023010007/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree041.table
  base := (-6719773249783161593249233899162489896419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-349629324055647875556691870938438000000000000)
      constant := (3619763278252586162121996206175423144688890829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree041.table
  base := (-1344081000996178583831805522343678419193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-14998322313590573530525874682435109362000000000000)
      constant := (155463264224270837639415983877357282460601674540435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158041290866511505003/50000000000000000000)
  centralHi := (316082581733023010007/100000000000000000000)
  directionLo := (320009223987197751357/100000000000000000000)
  directionHi := (160004611993598875679/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree042.table
  base := (-6576299043304905190165315370745960890961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-358149994048778439216414169451278000000000000)
      constant := (3803383958534039201209957284933952100907794751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree042.table
  base := (-6576845316759789384377216888164641036243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-1707093387518442669037482705182865558000000000000)
      constant := (18149894336825990932885578963931780965976577039893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320009223987197751357/100000000000000000000)
  centralHi := (160004611993598875679/50000000000000000000)
  directionLo := (161944132649784374627/50000000000000000000)
  directionHi := (64777653059913749851/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree043.table
  base := (-256137229605639506229689725881697250931/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-366670664041909002876136467964118000000000000)
      constant := (3991700903210880126754521482344620846621825525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree043.table
  base := (-160097571955114121218315320459230708081/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-15729358661741394512148814010856470682000000000000)
      constant := (171436487259299257682716580516263355795541583347160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161944132649784374627/50000000000000000000)
  centralHi := (64777653059913749851/20000000000000000000)
  directionLo := (163860697972881190263/50000000000000000000)
  directionHi := (327721395945762380527/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree044.table
  base := (-387590445975277385916810524098755275071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-375191334035039566535858766476958000000000000)
      constant := (4184711154543633012135323715577212884588348176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree044.table
  base := (-1240371003486551745144319659795979070467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-16094876835816805002960283675067151342000000000000)
      constant := (179725452838653173392551724227564951481083084579265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163860697972881190263/50000000000000000000)
  centralHi := (327721395945762380527/100000000000000000000)
  directionLo := (331510208474059646941/100000000000000000000)
  directionHi := (165755104237029823471/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree045.table
  base := (-373161458042609450741994309099420453929/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-383712004028170130195581064989798000000000000)
      constant := (4382412218367150137573959617563137974468275824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree045.table
  base := (-5970935548902143196734385122639771167703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-203214753208545870293478436287380642000000000000)
      constant := (2323652339270873984760860653636215499203692763817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331510208474059646941/100000000000000000000)
  centralHi := (165755104237029823471/50000000000000000000)
  directionLo := (335256205437557587699/100000000000000000000)
  directionHi := (3352562054375575877/1000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree046.table
  base := (-2855518801480686289855788374540267488869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-392232674021300693855303363502638000000000000)
      constant := (4584801991090841681447096517321832604421177558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree046.table
  base := (-5711341632927512096065669926971088253617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (104838138)
      previous := (52419069)
      next := (52419069)
      square := (670641035402719741632671098987020000000000000)
      linear := (-31807019251356570859325563333626678000000000000)
      constant := (372226006729739757417544697145695279702107557007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335256205437557587699/100000000000000000000)
  centralHi := (3352562054375575877/1000000000000000000)
  directionLo := (2711686450856914507/800000000000000000)
  directionHi := (10592525198659822293/3125000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree047.table
  base := (-2711488608728848763052302422405096210087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-400753344014431257515025662015478000000000000)
      constant := (4791878698263823924569586854838994668614374034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree047.table
  base := (-542323954733879275145942117862745215251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-17191431358043036475394692667699193322000000000000)
      constant := (205800531488513655211996507421266557653525703397090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2711686450856914507/800000000000000000)
  centralHi := (10592525198659822293/3125000000000000000)
  directionLo := (42828169250823632933/12500000000000000000)
  directionHi := (68525070801317812693/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree048.table
  base := (-1021308656270621021358977357982949840799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-409274014007561821174747960528318000000000000)
      constant := (5003640842858781007539043663366978425694817045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree048.table
  base := (-5106769545123857547346042856121948186619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-1950772170235382996245129147989985998000000000000)
      constant := (23877188612163835671066304209321753944287325137069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42828169250823632933/12500000000000000000)
  centralHi := (68525070801317812693/20000000000000000000)
  directionLo := (86562780024823531863/25000000000000000000)
  directionHi := (346251120099294127453/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree049.table
  base := (-2380927429316933129558289907961291396999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-417794684000692384834470259041158000000000000)
      constant := (5220087161725882581981288868836499319138475218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree049.table
  base := (-1190512485963346745489447035407867740327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-17922467706193857457017631996120554642000000000000)
      constant := (224190001837517210341995026937618222394163493406372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/25000000000000000000)
  centralHi := (346251120099294127453/100000000000000000000)
  directionLo := (87459827610984895743/25000000000000000000)
  directionHi := (349839310443939582973/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree050.table
  base := (-4389012425122464917423655138613895211427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-426315353993822948494192557553998000000000000)
      constant := (5441216588917127915836761190619345185701970957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree050.table
  base := (-1097295142304214308414909397731193373677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-18287985880269267947829101660331235302000000000000)
      constant := (233686399093376579737380806583525526962992450536972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87459827610984895743/25000000000000000000)
  centralHi := (349839310443939582973/100000000000000000000)
  directionLo := (176695534814668183411/50000000000000000000)
  directionHi := (353391069629336366823/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree051.table
  base := (-3988100780752606038871893809652969032573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-434836023986953512153914856066838000000000000)
      constant := (5667028224790020333214994947538409651533433043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree051.table
  base := (-797649131070080976579140823164379069137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-2072611561593853159848952369393546218000000000000)
      constant := (27042650109497155553194587772821039681953786122435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176695534814668183411/50000000000000000000)
  centralHi := (353391069629336366823/100000000000000000000)
  directionLo := (356907485289453958161/100000000000000000000)
  directionHi := (178453742644726979081/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree052.table
  base := (-1779595751732403214996139743004182118297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-443356693980084075813637154579678000000000000)
      constant := (5897521309974188891315502933976913263813974254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree052.table
  base := (-3559316288178736511754767757456934721401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-19019022228420088929452040988752596622000000000000)
      constant := (253282325199212673801574679112570787197937602837559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356907485289453958161/100000000000000000000)
  centralHi := (178453742644726979081/50000000000000000000)
  directionLo := (180194795996941267681/50000000000000000000)
  directionHi := (360389591993882535363/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree053.table
  base := (-3102345017296208506922311346641942129621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-451877363973214639473359453092518000000000000)
      constant := (6132695203431023546245482421145249635946850811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree053.table
  base := (-775613116049958512320395827457642548101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-19384540402495499420263510652963277282000000000000)
      constant := (263381794461080906234218905106204072122032649771436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180194795996941267681/50000000000000000000)
  centralHi := (360389591993882535363/100000000000000000000)
  directionLo := (363838374803143122377/100000000000000000000)
  directionHi := (181919187401571561189/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree054.table
  base := (-327201541957718650170588393546349971761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-460398033966345203133081751605358000000000000)
      constant := (6372549363959205232096499276361346185196700408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree054.table
  base := (-1308852412787997549624192686963341695663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-243827883661369258161419510088567382000000000000)
      constant := (3378793033949502134466900801426411548611852484514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363838374803143122377/100000000000000000000)
  centralHi := (181919187401571561189/50000000000000000000)
  directionLo := (73450954504694568033/20000000000000000000)
  directionHi := (183627386261736420083/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree055.table
  base := (-421007306222245106701494170313600289729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-468918703959475766792804050118198000000000000)
      constant := (6617083334602053152281378965609605072631325195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree055.table
  base := (-2105116122693486588950946637706210142463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-20115576750646320401886449981384638602000000000000)
      constant := (284183629632012879857393165694093174926433841304017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73450954504694568033/20000000000000000000)
  centralHi := (183627386261736420083/50000000000000000000)
  directionLo := (370639680691562099081/100000000000000000000)
  directionHi := (185319840345781049541/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree056.table
  base := (-1564653974694567537573420052317293642769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-477439373952606330452526348631038000000000000)
      constant := (6866296729499098599067051617013173831743863679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree056.table
  base := (-1564722447211924659846801632445360139859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-20481094924721730892697919645595319262000000000000)
      constant := (294885959700661960769232772307206479022562430750781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370639680691562099081/100000000000000000000)
  centralHi := (185319840345781049541/50000000000000000000)
  directionLo := (186996977158066942889/50000000000000000000)
  directionHi := (373993954316133885779/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree057.table
  base := (-199299076244464231728410386989515735957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-485960043945736894112248647143878000000000000)
      constant := (7120189222796916490522168844943507137786160935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree057.table
  base := (-249138567947446151422625281642013576377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-2316290344310793487056598812200666658000000000000)
      constant := (33976579122604690361880987249986519792026713254908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186996977158066942889/50000000000000000000)
  centralHi := (373993954316133885779/100000000000000000000)
  directionLo := (377318410400147012567/100000000000000000000)
  directionHi := (47164801300018376571/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree058.table
  base := (-100146672739558018734576506612380210369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-494480713938867457771970945656718000000000000)
      constant := (7378760539295248748746442265958761033392781116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree058.table
  base := (-200318663466167800331470326839808124937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-21212131272872551874320858974016680582000000000000)
      constant := (316893375143650844582220445984549079332186761465166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377318410400147012567/100000000000000000000)
  centralHi := (47164801300018376571/12500000000000000000)
  directionLo := (380613830264704252169/100000000000000000000)
  directionHi := (38061383026470425217/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree059.table
  base := (44610037310216350232675550667933817857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-503001383931998021431693244169558000000000000)
      constant := (7642010446555715303777041446949382549368224565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree059.table
  base := (223006659414277950800438352158149118219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-21577649446947962365132328638227361242000000000000)
      constant := (328198438944088565845225248785061598253389697961979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380613830264704252169/100000000000000000000)
  centralHi := (38061383026470425217/10000000000000000000)
  directionLo := (383880961693393213561/100000000000000000000)
  directionHi := (191940480846696606781/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree060.table
  base := (874396744866110830559089379789243023207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-511522053925128585091415542682398000000000000)
      constant := (7909938748243499399444063006464064079233203063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree060.table
  base := (87435933795219490327952299107412441911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-2438129735669263650660422033604226878000000000000)
      constant := (37744932795937672946215576074067077122566691170390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383880961693393213561/100000000000000000000)
  centralHi := (191940480846696606781/50000000000000000000)
  directionLo := (12097516278554146889/3125000000000000000)
  directionHi := (387120520913732700449/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree061.table
  base := (1553437351036274638766074487916358364211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-520042723918259148751137841195238000000000000)
      constant := (8182545278508628326963269403444702645885914499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree061.table
  base := (1553405211641161284665890592178994195781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-22308685795098783346755267966648722562000000000000)
      constant := (351411236756979637363803933452883817907827867912021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097516278554146889/3125000000000000000)
  centralHi := (387120520913732700449/100000000000000000000)
  directionLo := (390333194430598083097/100000000000000000000)
  directionHi := (195166597215299041549/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree062.table
  base := (2260158798618662021690486430153847727163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-528563393911389712410860139708078000000000000)
      constant := (8459829897243949241900879018807258170537472267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree062.table
  base := (565032797882659309869373475449685474473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-22674203969174193837566737630859403222000000000000)
      constant := (363318957774669190581640054618326629453401652633572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390333194430598083097/100000000000000000000)
  centralHi := (195166597215299041549/50000000000000000000)
  directionLo := (78703928144984076311/20000000000000000000)
  directionHi := (98379910181230095389/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree063.table
  base := (2994549930396019361431536109308138732447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-537084063904520276070582438220918000000000000)
      constant := (8741792486082544300624582381019604043812530223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree063.table
  base := (299452622192802734114131399667229538299/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-284441014114192646029360583889754122000000000000)
      constant := (4634908064083398078939054813163058251928896541390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78703928144984076311/20000000000000000000)
  centralHi := (98379910181230095389/25000000000000000000)
  directionLo := (6198132684836956281/1562500000000000000)
  directionHi := (79336098365913040397/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree064.table
  base := (3756601319890756414065281203917226939483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-545604733897650839730304736733758000000000000)
      constant := (9028432945018912748236590385993349860600975147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree064.table
  base := (751316192808986542139180450338056495603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-23405240317325014819189676959280764542000000000000)
      constant := (387737018759964291606357045035862347187570030373615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6198132684836956281/1562500000000000000)
  centralHi := (79336098365913040397/20000000000000000000)
  directionLo := (399816354793073809111/100000000000000000000)
  directionHi := (49977044349134226139/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree065.table
  base := (1136576250621114304737873891901531470083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-554125403890781403390027035246598000000000000)
      constant := (9319751189556417809810470874541603389464442188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree065.table
  base := (2273143764485378250298824721951115281791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-23770758491400425310001146623491445202000000000000)
      constant := (400247350896115585105245787779387597060737376576862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399816354793073809111/100000000000000000000)
  centralHi := (49977044349134226139/12500000000000000000)
  directionLo := (402927813040867660997/100000000000000000000)
  directionHi := (201463906520433830499/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree066.table
  base := (5363654248394619272985051005378301662223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-562646073883911967049749333759438000000000000)
      constant := (9615747148298796916290781541643646402334523807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree066.table
  base := (670454906532562642680285780520895197761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-2681808518386203977868068476411347318000000000000)
      constant := (45884282952183569158710791997580097113405233149512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402927813040867660997/100000000000000000000)
  centralHi := (201463906520433830499/50000000000000000000)
  directionLo := (203007713821280528221/50000000000000000000)
  directionHi := (406015427642561056443/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree067.table
  base := (3104321685487552962985429183854119744733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-571166743877042530709471632272278000000000000)
      constant := (9916420760916421203955602686512162712743744794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree067.table
  base := (1241726100726827779264019312661869258869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-24501794839551246291624085951912806522000000000000)
      constant := (425870603221132826325546825130665869534898019893145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203007713821280528221/50000000000000000000)
  centralHi := (406015427642561056443/100000000000000000000)
  directionLo := (204539869246589100109/50000000000000000000)
  directionHi := (409079738493178200219/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree068.table
  base := (7081267564830195263763503156386929273503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-579687413870173094369193930785118000000000000)
      constant := (10221771976428847459017765606735652932662593327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree068.table
  base := (3540628263152291369551822132764686241469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-24867313013626656782435555616123487182000000000000)
      constant := (438983518688193443812652170609705326232860642530458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204539869246589100109/50000000000000000000)
  centralHi := (409079738493178200219/100000000000000000000)
  directionLo := (412121265415317280729/100000000000000000000)
  directionHi := (41212126541531728073/10000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree069.table
  base := (498845173068404681567916264653883865613/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-588208083863303658028916229297958000000000000)
      constant := (10531800751754354521524309768936190862884613072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree069.table
  base := (3990756650655160292600091734322498059309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (11648682)
      previous := (5824341)
      next := (5824341)
      square := (74515670600302193514741233220780000000000000)
      linear := (-5299901530708268698434577878667122000000000000)
      constant := (95000481231647593182381133282962580874401765258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412121265415317280729/100000000000000000000)
  centralHi := (41212126541531728073/10000000000000000000)
  directionLo := (415140509188633289509/100000000000000000000)
  directionHi := (41514050918863328951/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree070.table
  base := (1113675693994706561139909306063822674251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-596728753856434221688638527810798000000000000)
      constant := (10846507050484866999819284598991108758009030872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree070.table
  base := (1781879486590529566655618136010036240267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-25598349361777477764058494944544848502000000000000)
      constant := (465811919044541233456696815262121555393466300229735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415140509188633289509/100000000000000000000)
  centralHi := (41514050918863328951/10000000000000000000)
  directionLo := (418137952512413120659/100000000000000000000)
  directionHi := (20906897625620656033/5000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree071.table
  base := (1972982602625209793448689998754326094997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-605249423849564785348360826323638000000000000)
      constant := (11165890841851169252875902840307701227709115865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree071.table
  base := (9864906052047525369488975573403430823037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-25963867535852888254869964608755529162000000000000)
      constant := (479527401085906426701678515531231497032230938389517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418137952512413120659/100000000000000000000)
  centralHi := (20906897625620656033/5000000000000000000)
  directionLo := (421114060906482175431/100000000000000000000)
  directionHi := (52639257613310271929/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree072.table
  base := (1084804270142912926560839458980526809041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-613770093842695349008083124836478000000000000)
      constant := (11489952099848793074095681437582780089171159690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree072.table
  base := (10848036734216380061559049558216708242777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-325054144567016033897301657690940862000000000000)
      constant := (6091897977356586886535870342689905383548491611097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421114060906482175431/100000000000000000000)
  centralHi := (52639257613310271929/12500000000000000000)
  directionLo := (212034641777601820093/50000000000000000000)
  directionHi := (424069283555203640187/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree073.table
  base := (11858792545215053398661150347418929786361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-622290763835825912667805423349318000000000000)
      constant := (11818690802499584093071889060569901426103503849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree073.table
  base := (11858787430873770381182286960044460935853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-26694903884003709236492903937176890482000000000000)
      constant := (507560923353216269850729664600309188352347634374973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212034641777601820093/50000000000000000000)
  centralHi := (424069283555203640187/100000000000000000000)
  directionLo := (427004054098903184897/100000000000000000000)
  directionHi := (213502027049451592449/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree074.table
  base := (1612145099193331006738267836259572232029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-630811433828956476327527721862158000000000000)
      constant := (12152106931227849838132260158586594414476765288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree074.table
  base := (3224289102733869606404663544385397326007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-27060422058079119727304373601387571142000000000000)
      constant := (521878961860979632655881003871503214130976729845148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427004054098903184897/100000000000000000000)
  centralHi := (213502027049451592449/50000000000000000000)
  directionLo := (8598375827533345663/2000000000000000000)
  directionHi := (429918791376667283151/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree075.table
  base := (13635884732928840026517657146590580099/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-639332103822087039987250020374998000000000000)
      constant := (12490200470333280487178990546600065771412777984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree075.table
  base := (13963142211578962068808543146253343429007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-3047326692461614468679538140622027978000000000000)
      constant := (59599761224910708992973386830115591141006914187143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8598375827533345663/2000000000000000000)
  centralHi := (429918791376667283151/100000000000000000000)
  directionLo := (86562780024823531863/20000000000000000000)
  directionHi := (108203475031029414829/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree076.table
  base := (3011349362656482298014116528150203640643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-647852773815217603646972318887838000000000000)
      constant := (12832971406545607389694960761826695552117907935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree076.table
  base := (3011348719329642749488071154404942742049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-27791458406229940708927312929808932462000000000000)
      constant := (551117590280928485312803784483513529866984985445045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/20000000000000000000)
  centralHi := (108203475031029414829/25000000000000000000)
  directionLo := (435689771629453134761/100000000000000000000)
  directionHi := (217844885814726567381/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree077.table
  base := (16177962276571390372338418604488509094059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-656373443808348167306694617400678000000000000)
      constant := (13180419728648305146562495319115944592978871931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree077.table
  base := (3235591904302901571247299402526086703851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-28156976580305351199738782594019613122000000000000)
      constant := (566038179156303353724958047550271473363198308464455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435689771629453134761/100000000000000000000)
  centralHi := (217844885814726567381/50000000000000000000)
  directionLo := (87709356870153906051/20000000000000000000)
  directionHi := (27409174021923095641/6250000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree078.table
  base := (17326791462733941316099272467061923753041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-664894113801478730966416915913518000000000000)
      constant := (13532545427160618336944635340392783949096011969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree078.table
  base := (8663394551694830940613821034904912437059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-3169166083820084632283361362025588198000000000000)
      constant := (64573290805446520447866115787239389303178194540982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87709356870153906051/20000000000000000000)
  centralHi := (27409174021923095641/6250000000000000000)
  directionLo := (88277060899482983239/20000000000000000000)
  directionHi := (110346326124353729049/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree079.table
  base := (18503233616403315903710327963284018021383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-673414783794609294626139214426358000000000000)
      constant := (13889348494068861126878608187899842147188852247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree079.table
  base := (18503231596244665164220198626372186740207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-28888012928456172181361721922440974442000000000000)
      constant := (596481904219940847833070396938715201128556655443487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88277060899482983239/20000000000000000000)
  centralHi := (110346326124353729049/25000000000000000000)
  directionLo := (111051421644477106377/25000000000000000000)
  directionHi := (444205686577908425509/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree080.table
  base := (3941457619818885219423300759571322500801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-681935453787739858285861512939198000000000000)
      constant := (14250828922599345217368687504175300802054989045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree080.table
  base := (4926821592404593560636843488489810780143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-29253531102531582672173191586651655102000000000000)
      constant := (612005039782471640381900846169194316806294190563452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111051421644477106377/25000000000000000000)
  centralHi := (444205686577908425509/100000000000000000000)
  directionLo := (223504136958371725133/50000000000000000000)
  directionHi := (447008273916743450267/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree081.table
  base := (327171162048678129818423444973942697487/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-690456123780870421945583811452038000000000000)
      constant := (14616986707026479542738431626303785716968933312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree081.table
  base := (418779057814245054660936210315857920453/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-365667275019839421765242731492127602000000000000)
      constant := (7749741033264306384824772071186159507135371446650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223504136958371725133/50000000000000000000)
  centralHi := (447008273916743450267/100000000000000000000)
  directionLo := (1799173596568832141/400000000000000000)
  directionHi := (449793399142208035251/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree082.table
  base := (11099115988140178265854990421236984406233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-698976793774000985605306109964878000000000000)
      constant := (14987821842510588080788434207131122335131451794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree082.table
  base := (22198230709261064251977539736643541869549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-29984567450682403653796130915073016422000000000000)
      constant := (643653855751068537257409891796218550017154148816509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1799173596568832141/400000000000000000)
  centralHi := (449793399142208035251/100000000000000000000)
  directionLo := (226280692323592315693/50000000000000000000)
  directionHi := (452561384647184631387/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree083.table
  base := (2935640066123644703914708003351262132433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-707497463767131549265028408477718000000000000)
      constant := (15363334324960838976645083426176742319703853576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree083.table
  base := (23485119444748721089212426673055456654513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-30350085624757814144607600579283697082000000000000)
      constant := (659779535779473879308843168506129853644565514940033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226280692323592315693/50000000000000000000)
  centralHi := (452561384647184631387/100000000000000000000)
  directionLo := (56914067878092035627/12500000000000000000)
  directionHi := (455312543024736285017/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree084.table
  base := (4959923940661463652214056694863718465301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-716018133760262112924750706990558000000000000)
      constant := (15743524150919393275271266311137197945991891545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree084.table
  base := (24799618775605435929758276195395805000951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-3412844866537024959491007804832708638000000000000)
      constant := (75122895959271558708239878485898632019509479485999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56914067878092035627/12500000000000000000)
  centralHi := (455312543024736285017/100000000000000000000)
  directionLo := (91609435496029045219/20000000000000000000)
  directionHi := (28627948592509076631/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree085.table
  base := (26141729223736155660819496928178691950543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-724538803753392676584473005503398000000000000)
      constant := (16128391317463485451264569099009877742903310687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree085.table
  base := (6535432107519711752232689439299657871521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-31081121972908635126230539907705058402000000000000)
      constant := (692633439189444425938711246643569274859245386069444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91609435496029045219/20000000000000000000)
  centralHi := (28627948592509076631/6250000000000000000)
  directionLo := (460765582220941269429/100000000000000000000)
  directionHi := (46076558222094126943/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree086.table
  base := (13755724428705675748601294121389443657753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-733059473746523240244195304016238000000000000)
      constant := (16517935822122657951426346734205989215530203154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree086.table
  base := (27511448178519514843974083368262791314359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-31446640146984045617042009571915739062000000000000)
      constant := (709361662343079872139604630641061718690412329903719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460765582220941269429/100000000000000000000)
  centralHi := (46076558222094126943/10000000000000000000)
  directionLo := (463468042826340205183/100000000000000000000)
  directionHi := (3620844084580782853/781250000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree087.table
  base := (7227194601877174330185207140838462786991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-741580143739653803903917602529078000000000000)
      constant := (16912157662808802748316079382305327006828750076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree087.table
  base := (3613597228357686591460410449119122043547/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-3534684257895495123094831026236268858000000000000)
      constant := (80698970334014543404228756944806999584266503804824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463468042826340205183/100000000000000000000)
  centralHi := (3620844084580782853/781250000000000000)
  directionLo := (116538709149351328261/25000000000000000000)
  directionHi := (93230967319481062609/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree088.table
  base := (3791714713458761885140143341500653212751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-750100813732784367563639901041918000000000000)
      constant := (17311056837757026779717995671393747439472602872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree088.table
  base := (6066743442222542128607064842884916532727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-32177676495134866598664948900337100382000000000000)
      constant := (743420651104049139556255485030764400397556405684035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116538709149351328261/25000000000000000000)
  centralHi := (93230967319481062609/20000000000000000000)
  directionLo := (46882623288914729531/10000000000000000000)
  directionHi := (468826232889147295311/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree089.table
  base := (1986641663580741118317260950656758136727/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-758621483725914931223362199554758000000000000)
      constant := (17714633345475665531466294099258222753160587888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree089.table
  base := (15893133096349329620653525428456386641753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-32543194669210277089476418564547781042000000000000)
      constant := (760751416573840719885805470286009543284506279633746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46882623288914729531/10000000000000000000)
  centralHi := (468826232889147295311/100000000000000000000)
  directionLo := (235741246712844200559/50000000000000000000)
  directionHi := (471482493425688401119/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree090.table
  base := (33266425017541833169087706766070668640957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-767142153719045494883084498067598000000000000)
      constant := (18122887184704028696759994005366063723611912813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree090.table
  base := (33266424654527141278921049770978683372979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-406280405472662809633183805293314342000000000000)
      constant := (9608432461262682349878255586284392528657181197619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235741246712844200559/50000000000000000000)
  centralHi := (471482493425688401119/100000000000000000000)
  directionLo := (474123872599534515009/100000000000000000000)
  directionHi := (47412387259953451501/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree091.table
  base := (34774192807992549474427989154924837622531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-775662823712176058542806796580438000000000000)
      constant := (18535818354376681231148068666163135602337431379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree091.table
  base := (34774192497662366785032868377860785541699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-33274231017361098071099357892969142362000000000000)
      constant := (796015489424384060778991467359704290349765447124659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474123872599534515009/100000000000000000000)
  centralHi := (47412387259953451501/10000000000000000000)
  directionLo := (119187654438980949809/25000000000000000000)
  directionHi := (476750617755923799237/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree092.table
  base := (36309569903775060208283645066726029000609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-784183493705306622202529095093278000000000000)
      constant := (18953426853593248480142488961763992441667460881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree092.table
  base := (726191392770279859706334213738001376187/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (104838138)
      previous := (52419069)
      next := (52419069)
      square := (670641035402719741632671098987020000000000000)
      linear := (-63591208301392265712496838482381518000000000000)
      constant := (1538655570363255523261045026805753625229869926150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119187654438980949809/25000000000000000000)
  centralHi := (476750617755923799237/100000000000000000000)
  directionLo := (479362969463151475749/100000000000000000000)
  directionHi := (1917451877852605903/400000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree093.table
  base := (37872556233172919745401016464987515433439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-792704163698437185862251393606118000000000000)
      constant := (19375712681592890672104938834059546551233354351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree093.table
  base := (37872556006461345060871285226198685803483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-3778363040612435450302477469043389298000000000000)
      constant := (92453661247056500117827205199105365968458048610867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479362969463151475749/100000000000000000000)
  centralHi := (1917451877852605903/400000000000000000)
  directionLo := (240980580884853470553/50000000000000000000)
  directionHi := (481961161769706941107/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree094.table
  base := (19731575867794100848095991997176594947561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-801224833691567749521973692118958000000000000)
      constant := (19802675837732724405968277924808824991597349298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree094.table
  base := (9865787885461354435018542159269037191577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-34370785539587329543533766885601184342000000000000)
      constant := (850417952901302957187627854735793041025054221598628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240980580884853470553/50000000000000000000)
  centralHi := (481961161769706941107/100000000000000000000)
  directionLo := (242272711224500557043/50000000000000000000)
  directionHi := (484545422449001114087/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree095.table
  base := (2567584772488875607051518950017097533851/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-809745503684698313181695990631798000000000000)
      constant := (20234316321469580590378353952593512203786004144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree095.table
  base := (20540678097135851645921055434548665363387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-34736303713662740034345236549811865002000000000000)
      constant := (868953801732636950823532546813187605411421118587734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242272711224500557043/50000000000000000000)
  centralHi := (484545422449001114087/100000000000000000000)
  directionLo := (121778993308102065419/25000000000000000000)
  directionHi := (487115973232408261677/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree096.table
  base := (10681792515655209697672089111388526767287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-818266173677828876841418289144638000000000000)
      constant := (20670634132344582790741263483900611521896591132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree096.table
  base := (42727169921175716766349599512371076799399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-3900202431970905613906300690446949518000000000000)
      constant := (98632277522017922648010956613603956380674327021151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121778993308102065419/25000000000000000000)
  centralHi := (487115973232408261677/100000000000000000000)
  directionLo := (489673030031297120221/100000000000000000000)
  directionHi := (244836515015648560111/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree097.table
  base := (44400592807447672660079690648475919414177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-826786843670959440501140587657478000000000000)
      constant := (21111629269970109801451711975986167029065003793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree097.table
  base := (2775037042913159121826081748609741743457/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-35467340061813561015968175878233226322000000000000)
      constant := (906628040781535087650529015896459759459180989227792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489673030031297120221/100000000000000000000)
  centralHi := (244836515015648560111/50000000000000000000)
  directionLo := (492216803148680551689/100000000000000000000)
  directionHi := (49221680314868055169/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree098.table
  base := (11525406140860766158462708688310350515133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-835307513664090004160862886170318000000000000)
      constant := (21557301734018773752605751908419222034460183988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree098.table
  base := (46101624460222053953942093046796820111391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-35832858235888971506779645542443906982000000000000)
      constant := (925766430968959765717753122228669876155006302302031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492216803148680551689/100000000000000000000)
  centralHi := (49221680314868055169/10000000000000000000)
  directionLo := (494747497481070913551/100000000000000000000)
  directionHi := (30921718592566932097/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree099.table
  base := (9566053060909365187176449561594961402711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-843828183657220567820585184683158000000000000)
      constant := (22007651524214102101477531071241326727606804995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree099.table
  base := (11957566304095671532477529111014148848631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-446893535925486197501124879094501082000000000000)
      constant := (11667971212947968333977677730511838344465927206364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494747497481070913551/100000000000000000000)
  centralHi := (30921718592566932097/6250000000000000000)
  directionLo := (124316328177772367603/25000000000000000000)
  directionHi := (497265312711089470413/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree100.table
  base := (1983460600350219591163775643921504461669/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-852348853650351131480307483195998000000000000)
      constant := (22462678640322660068922922638228881020846160525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree100.table
  base := (49586514933459331571118088018878638924143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-36563894584039792488402584870865268302000000000000)
      constant := (964645752611178007045682284925555742549355741544863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124316328177772367603/25000000000000000000)
  centralHi := (497265312711089470413/100000000000000000000)
  directionLo := (499770443491342261389/100000000000000000000)
  directionHi := (49977044349134226139/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree101.table
  base := (12842593414373640071675097937900246296121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-860869523643481695140029781708838000000000000)
      constant := (22922383082147390828185094675084652851822190756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree101.table
  base := (51370373593194490985237974259058339180669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-36929412758115202979214054535075948962000000000000)
      constant := (984386684047837895633863878391365478769836323772429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499770443491342261389/100000000000000000000)
  centralHi := (49977044349134226139/10000000000000000000)
  directionLo := (251131539810020805063/50000000000000000000)
  directionHi := (502263079620041610127/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree102.table
  base := (2127273649403512069503837351061773150859/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-869390193636612258799752080221678000000000000)
      constant := (23386764849521985194498851493448234783936578275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree102.table
  base := (26590920590091607575579713867681451925079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-4143881214687845941113947133254069958000000000000)
      constant := (111592051394640249038161701246360675674511459142942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251131539810020805063/50000000000000000000)
  centralHi := (502263079620041610127/100000000000000000000)
  directionLo := (15773231444025678089/3125000000000000000)
  directionHi := (504743406208821698849/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree103.table
  base := (55020917728308567642845123000251227676923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (780424069713369084055898380000000000000)
      linear := (-82751518864147688044063943702000000000000)
      constant := (2248640205703282276865215589786251227676923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree103.table
  base := (27510458840715496496196309217385839229913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (33440390963148151882711189684620000000000000)
      linear := (-3549858526370630970010085197803498000000000000)
      constant := (96566225668493159941933782627075645650325084274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15773231444025678089/3125000000000000000)
  centralHi := (504743406208821698849/100000000000000000000)
  directionLo := (126802900960792029797/25000000000000000000)
  directionHi := (507211603843168119189/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree104.table
  base := (56887603126000488623543271548575195775477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-886431533622873386119196677247358000000000000)
      constant := (24329560360381442347736956937210146251982035493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree104.table
  base := (56887603085980062581327593038649446338427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-38025967280341434451648463527707990942000000000000)
      constant := (1044814560738701738420293634750203933636381137670507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126802900960792029797/25000000000000000000)
  centralHi := (507211603843168119189/100000000000000000000)
  directionLo := (127416962183963718739/25000000000000000000)
  directionHi := (509667848735854874957/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree105.table
  base := (11756379483751359739688432370744541789511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-894952203616003949778918975760198000000000000)
      constant := (24807974103648150831625443388774934219224610995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree105.table
  base := (2351275895383742293927429734900014185251/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-4265720606046316104717770354657630178000000000000)
      constant := (118373208934726301529341708648666130604730298417475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127416962183963718739/25000000000000000000)
  centralHi := (509667848735854874957/100000000000000000000)
  directionLo := (512112312873757776577/100000000000000000000)
  directionHi := (256056156436878888289/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree106.table
  base := (7587975074831154618951913604646508123619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-903472873609134513438641274273038000000000000)
      constant := (25291065172022136206871467466538666437467791768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree106.table
  base := (1517595014237213461692281345369542462763/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-38757003628492255433271402856129352262000000000000)
      constant := (1086104047135010852290332230673391819165454373131320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512112312873757776577/100000000000000000000)
  centralHi := (256056156436878888289/50000000000000000000)
  directionLo := (8039768189974849689/1562500000000000000)
  directionHi := (514545164158390380097/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree107.table
  base := (3915832041187428911110168338285637350491/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-911993543602265077098363572785878000000000000)
      constant := (25778833565432541590471601268014223226421744304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree107.table
  base := (62653312634110349362698559404228730103451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-39122521802567665924082872520340032922000000000000)
      constant := (1107050060903144505170201556945509165981455207076491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8039768189974849689/1562500000000000000)
  centralHi := (514545164158390380097/100000000000000000000)
  directionLo := (103393313308097489079/20000000000000000000)
  directionHi := (129241641635121861349/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree108.table
  base := (31557828903409328938056674038467081359/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-920514213595395640758085871298718000000000000)
      constant := (26271279283819708651032150075196415201049868288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree108.table
  base := (12926086714588379761635176373607761834111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-487506666378309585369065952895687822000000000000)
      constant := (13928357058202835620530265993850645907313431119355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103393313308097489079/20000000000000000000)
  centralHi := (129241641635121861349/25000000000000000000)
  directionLo := (259688340074470595589/50000000000000000000)
  directionHi := (519376680148941191179/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree109.table
  base := (66635163399467977299021336035365337944673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-929034883588526204417808169811558000000000000)
      constant := (26768402327133439961756784715926292870255035857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree109.table
  base := (13327032676268493691326630109492548924697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-39853558150718486905705811848761394242000000000000)
      constant := (1149544629566756791428318970325070878658639458287885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259688340074470595589/50000000000000000000)
  centralHi := (519376680148941191179/100000000000000000000)
  directionLo := (521775661414377292039/100000000000000000000)
  directionHi := (13044391535359432301/2500000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree110.table
  base := (34333751035438804493018696091722099132647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-937555553581656768077530468324398000000000000)
      constant := (27270202695331530072199352365412939499396504046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree110.table
  base := (34333751027705738401814116886881091109057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-40219076324793897396517281512972074902000000000000)
      constant := (1171093184458352677663183163308254023297870823632674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521775661414377292039/100000000000000000000)
  centralHi := (13044391535359432301/2500000000000000000)
  directionLo := (262081831593820244621/50000000000000000000)
  directionHi := (524163663187640489243/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree111.table
  base := (17681862401267301739722637330552853094943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-946076223574787331737252766837238000000000000)
      constant := (27776680388378523770482591856408638873937001148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree111.table
  base := (70727449591873338385552264296538203785673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-4509399388763256431925416797464750618000000000000)
      constant := (132538065154192034646141164836051733658664057324177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262081831593820244621/50000000000000000000)
  centralHi := (524163663187640489243/100000000000000000000)
  directionLo := (526540834853443774817/100000000000000000000)
  directionHi := (263270417426721887409/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree112.table
  base := (18203751499809527965522535568344058180919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-954596893567917895396975065350078000000000000)
      constant := (28287835406244666425504102722036904452965478684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree112.table
  base := (72815005987980154392376971442731957556419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-40950112672944718378140220841393436222000000000000)
      constant := (1214792835353634540191360378338634061821794990928179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526540834853443774817/100000000000000000000)
  centralHi := (263270417426721887409/50000000000000000000)
  directionLo := (2066044228278985427/390625000000000000)
  directionHi := (528907322439420269313/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree113.table
  base := (74930171251033365750160184050364273513339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-963117563561048459056697363862918000000000000)
      constant := (28803667748905016724420330216357168577703013451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree113.table
  base := (74930171241429475821129950762135564762293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-41315630847020128868951690505604116882000000000000)
      constant := (1236943931355024703917036228151893068951025118659013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2066044228278985427/390625000000000000)
  centralHi := (528907322439420269313/100000000000000000000)
  directionLo := (531263268720803065861/100000000000000000000)
  directionHi := (265631634360401532931/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree114.table
  base := (77072945358487020710545391511553891905363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-971638233554179022716419662375758000000000000)
      constant := (29324177416338696707826975340519967239223996067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree114.table
  base := (77072945350294807103560594418201017346159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-4631238780121726595529240018868310838000000000000)
      constant := (139921763821224782991713168011398947419393933356391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531263268720803065861/100000000000000000000)
  centralHi := (265631634360401532931/50000000000000000000)
  directionLo := (133402203330236345677/25000000000000000000)
  directionHi := (533608813320945382709/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree115.table
  base := (79243328319954388977138076825896565879159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-980158903547309586376141960888598000000000000)
      constant := (29849364408528257883213401634325706667411997831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree115.table
  base := (15848665662593375781777850626229552997149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (104838138)
      previous := (52419069)
      next := (52419069)
      square := (670641035402719741632671098987020000000000000)
      linear := (-79483302826410113139082476056758938000000000000)
      constant := (2423154375162378108604526882345768947737435265105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133402203330236345677/25000000000000000000)
  centralHi := (533608813320945382709/100000000000000000000)
  directionLo := (5359440928078812847/1000000000000000000)
  directionHi := (535944092807881284701/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree116.table
  base := (81441320134063543458987350625261725603863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-988679573540440150035864259401438000000000000)
      constant := (30379228725459145476071711112467889646931382567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree116.table
  base := (81441320128104023771565850877472114947309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-42412185369246360341386099498236158862000000000000)
      constant := (1304602301564039719536329406730159265561679174604669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5359440928078812847/1000000000000000000)
  centralHi := (535944092807881284701/100000000000000000000)
  directionLo := (107653848157423187783/20000000000000000000)
  directionHi := (134567310196778984729/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree117.table
  base := (83666920799672638906164967477845507659969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-997200243533570713695586557914278000000000000)
      constant := (30913770367119245650145415019160508990764611121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree117.table
  base := (4183346039729512298177367011386681520527/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-528119796831132973237007026696874562000000000000)
      constant := (16389589946912849780434991314134023182978446576940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107653848157423187783/20000000000000000000)
  centralHi := (134567310196778984729/25000000000000000000)
  directionLo := (540584387990823803043/100000000000000000000)
  directionHi := (135146096997705950761/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree118.table
  base := (42960065157916922426982645767438876483579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1005720913526701277355308856427118000000000000)
      constant := (31452989333498502872034451263683962081228579222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree118.table
  base := (1718402606229995898440861375193589996219/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-43143221717397181323009038826657520182000000000000)
      constant := (1350712116868180525130967428099215066474420197998950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540584387990823803043/100000000000000000000)
  centralHi := (135146096997705950761/25000000000000000000)
  directionLo := (271444831181811627277/50000000000000000000)
  directionHi := (108577932472724650911/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree119.table
  base := (88200948681762868268864041195777894619773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1014241583519831841015031154939958000000000000)
      constant := (31996885624588596576946160742537689684021171757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree119.table
  base := (88200948678067235727885831144252871188073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-43508739891472591813820508490868200842000000000000)
      constant := (1374068295068410843019416345972872103981397883415993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271444831181811627277/50000000000000000000)
  centralHi := (108577932472724650911/20000000000000000000)
  directionLo := (54518518914508690543/10000000000000000000)
  directionHi := (545185189145086905431/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree120.table
  base := (90509375896813201741115496863052896962053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1022762253512962404674753453452798000000000000)
      constant := (32545459240382667967770551116511888183870420277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree120.table
  base := (45254687946831082911145558458721242851103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-4874917562838666922736886461675431278000000000000)
      constant := (155291702255593912700838832051819944802008803144494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54518518914508690543/10000000000000000000)
  centralHi := (545185189145086905431/100000000000000000000)
  directionLo := (547471090949138166659/100000000000000000000)
  directionHi := (27373554547456908333/5000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree121.table
  base := (46422705980227183294959107477553568709281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1031282923506092968334475751965638000000000000)
      constant := (33098710180875089196182999870649409620873524258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree121.table
  base := (23211352989441964689767853783784515595863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-44239776239623412795443447819289562162000000000000)
      constant := (1421383192563748742882640921623520943401242085141532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547471090949138166659/100000000000000000000)
  centralHi := (27373554547456908333/5000000000000000000)
  directionLo := (68718435980059560941/12500000000000000000)
  directionHi := (549747487840476487529/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree122.table
  base := (95209056872253533138531964883920186900079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1039803593499223531994198050478478000000000000)
      constant := (33656638446061268372142969898641945262822938111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree122.table
  base := (95209056869963227041384598688824972151611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-44605294413698823286254917483500242822000000000000)
      constant := (1445341911858430008667674079722145090421363944651051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68718435980059560941/12500000000000000000)
  centralHi := (549747487840476487529/100000000000000000000)
  directionLo := (552014497408166059113/100000000000000000000)
  directionHi := (276007248704083029557/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree123.table
  base := (12200038828982499483308836514884485175999/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1048324263492354095653920348991318000000000000)
      constant := (34219244035937484860783624647976310025857387128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree123.table
  base := (97600310629907590136180266190006857020989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-4996756954197137086340709683078991498000000000000)
      constant := (163277942020470460376507149354666207828351935825061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552014497408166059113/100000000000000000000)
  centralHi := (276007248704083029557/50000000000000000000)
  directionLo := (554272234836515604153/100000000000000000000)
  directionHi := (277136117418257802077/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree124.table
  base := (10001917323899206184904743420178632027267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1056844933485484659313642647504158000000000000)
      constant := (34786526950500750181866960133927223071772756030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree124.table
  base := (100019173237327813257668772270847722489751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-45336330761849644267877856811921604142000000000000)
      constant := (1493861891541036984057515002876160097860760080414791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554272234836515604153/100000000000000000000)
  centralHi := (277136117418257802077/50000000000000000000)
  directionLo := (278260406486685072263/50000000000000000000)
  directionHi := (556520812973370144527/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree125.table
  base := (102465644693425979129660671118817631775971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1065365603478615222973364946016998000000000000)
      constant := (35358487189748690550885390830674286255511276339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree125.table
  base := (51232822346003724856733070831331954482929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-45701848935925054758689326476132284802000000000000)
      constant := (1518423151928740137245994371989380225226464826530178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278260406486685072263/50000000000000000000)
  centralHi := (556520812973370144527/100000000000000000000)
  directionLo := (558760342395929312833/100000000000000000000)
  directionHi := (279380171197964656417/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree126.table
  base := (104939724994986589363685695011281643630109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1073886273471745786633087244529838000000000000)
      constant := (35935124753679447712960793212542554957271826381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree126.table
  base := (20987944998755515283101375522712603206409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (684683642)
      previous := (342341821)
      next := (342341821)
      square := (4379865527506651152144234708199180000000000000)
      linear := (-568732927283956361104948100498061302000000000000)
      constant := (19051669868484775469692448778765578751617417699245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558760342395929312833/100000000000000000000)
  centralHi := (279380171197964656417/50000000000000000000)
  directionLo := (560990931474200828667/100000000000000000000)
  directionHi := (140247732868550207167/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree127.table
  base := (107441414143539437853358165610979293592371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1082406943464876350292809543042678000000000000)
      constant := (36516439642291595238204585393626705325721463939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree127.table
  base := (107441414142509060180046892163568144633503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-46432885284075875740312265804553646122000000000000)
      constant := (1568148213796558309441170173389261353808514891228623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560990931474200828667/100000000000000000000)
  centralHi := (140247732868550207167/25000000000000000000)
  directionLo := (563212686432192167483/100000000000000000000)
  directionHi := (140803171608048041871/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree128.table
  base := (54985356069492057668807022434556056095799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1090927613458006913952531841555518000000000000)
      constant := (37102431855584067884766138994267034398240663182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree128.table
  base := (109970712138106033036062220216123896571/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (55459375002)
      previous := (27729687501)
      next := (27729687501)
      square := (354769107728038743323683011364133580000000000000)
      linear := (-46798403458151286231123735468764326782000000000000)
      constant := (1593312015276571046288701322931728445359807794411000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell085.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563212686432192167483/100000000000000000000)
  centralHi := (140803171608048041871/25000000000000000000)
  directionLo := (113085142281387637383/20000000000000000000)
  directionHi := (141356427851734546729/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree129.table
  base := (112527618981248640773705265737379074337411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1294298)
      previous := (647149)
      next := (647149)
      square := (8279518955589132612749025913420000000000000)
      linear := (-1099448283451137477612254140068358000000000000)
      constant := (37693101393556102005762939771148116599645593299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree129.table
  base := (112527618980500389077818940785608440466037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (6162152778)
      previous := (3081076389)
      next := (3081076389)
      square := (39418789747559860369298112373792620000000000000)
      linear := (-5240435736914077413548356125886111938000000000000)
      constant := (179852962643030451517970155900119276989688832083613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell085.Kernel129
