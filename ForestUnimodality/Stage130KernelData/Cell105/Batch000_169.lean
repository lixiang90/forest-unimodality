import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell105.Parameters
import ForestUnimodality.BinomialMassData.Q27_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q27_52.Batch050_099
import ForestUnimodality.BinomialMassData.Q27_52.Batch100_149
import ForestUnimodality.BinomialMassData.Q27_52.Batch150_199
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch000_049
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch050_099
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch100_149
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree000.table
  base := (739309937296127287942226761/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361591850362212585690002695000000000000)
      linear := (-16510498564721331517246572000000000000)
      constant := (369654968648063643971113380500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree000.table
  base := (739309937296127287942226761/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361591850362212585690002695000000000000)
      linear := (-16510498564721331517246572000000000000)
      constant := (369654968648063643971113380500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree001.table
  base := (406916209209952955777317341426348792456319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-132499287992012427630020287281000000000000)
      constant := (68804687006344414741918908970020820925117911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree001.table
  base := (406549246082387047576445224065334806442333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-5793841680388058173777664526985829750000000000)
      constant := (3002751908829900691142171457998808095822263073637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (390318417364746481/781250000000000000)
  directionHi := (49960757422687549569/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree002.table
  base := (238303680657963947436099075991152505036887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-259418027469149045207211233226000000000000)
      constant := (40410917445649150791547303371604273351233903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree002.table
  base := (59483173653237687211023121881920751214057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-5671959710548913044318845297536921750000000000)
      constant := (881231836632586079695458689867553179052428650146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390318417364746481/781250000000000000)
  centralHi := (49960757422687549569/100000000000000000000)
  directionLo := (17663795183399252579/25000000000000000000)
  directionHi := (70655180733597010317/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree003.table
  base := (150038086706093991333264006446239136020019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-386336766946285662784402179171000000000000)
      constant := (25661679947102519913204460869809288987383211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree003.table
  base := (149748483447746709998043486170034060953961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-16893997161807594003497716663161857250000000000)
      constant := (1118819095193486078627429847529847708798252504529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17663795183399252579/25000000000000000000)
  centralHi := (70655180733597010317/100000000000000000000)
  directionLo := (86534570240718750803/100000000000000000000)
  directionHi := (21633642560179687701/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree004.table
  base := (50838927621187421106801842947192706537181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-256627753211711140180796562558000000000000)
      constant := (8861174411890944329380076969502567404783589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree004.table
  base := (10146829212307101392116966222138715704589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-11222037451258680959178871365624935500000000000)
      constant := (386317252965629431522221211737931246322368532105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86534570240718750803/100000000000000000000)
  centralHi := (21633642560179687701/25000000000000000000)
  directionLo := (390318417364746481/390625000000000000)
  directionHi := (99921514845375099137/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree005.table
  base := (18382630260867003089624545441977131383509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-320087122950279448969392035530500000000000)
      constant := (6632448726471526301883806987626707907626042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree005.table
  base := (36690113200089512742237067199832885578589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-13997076321613564916608884399668942375000000000)
      constant := (289197473924745183923586824613213859807804242421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390318417364746481/390625000000000000)
  centralHi := (99921514845375099137/100000000000000000000)
  directionLo := (2234312996090131093/2000000000000000000)
  directionHi := (111715649804506554651/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree006.table
  base := (27964467922848458816869411362849165570619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-383546492688847757757987508503000000000000)
      constant := (5327788889012334514772787760953258981434611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree006.table
  base := (55818384776877160041703910804174941256903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-33544230383936897748077794867425898500000000000)
      constant := (464745875793753855947950422054334018146979810367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2234312996090131093/2000000000000000000)
  centralHi := (111715649804506554651/100000000000000000000)
  directionLo := (122378362848551681721/100000000000000000000)
  directionHi := (61189181424275840861/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree007.table
  base := (2203543289360331198564084064721425622547/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-447005862427416066546582981475500000000000)
      constant := (4541406138186627039297307417986146802104430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree007.table
  base := (10996533953136768906638956176406043381309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-19547154062323332831468910467756956125000000000)
      constant := (198139064784603255959543882091060028003461699002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122378362848551681721/100000000000000000000)
  centralHi := (61189181424275840861/50000000000000000000)
  directionLo := (132183739452855560237/100000000000000000000)
  directionHi := (66091869726427780119/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree008.table
  base := (35523185114175607720134528961235551962573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-1020930464331968750670356908896000000000000)
      constant := (8135402695592970253897045298776808281674837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree008.table
  base := (7091078507104975679488232480949105331601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-44644385865356433577797847003601926000000000000)
      constant := (355067355051284993335425889686270655641265472445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132183739452855560237/100000000000000000000)
  centralHi := (66091869726427780119/50000000000000000000)
  directionLo := (141310361467194020633/100000000000000000000)
  directionHi := (70655180733597010317/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree009.table
  base := (14508035290036081721948847408250521596359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-573924601904552684123773927420500000000000)
      constant := (3799374453509979668350661263297275649784671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree009.table
  base := (1447992109236105374425153121062667526999/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-25097231803033100746328936535844969875000000000)
      constant := (165882759367899272606096192929322701238258959110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141310361467194020633/100000000000000000000)
  centralHi := (70655180733597010317/50000000000000000000)
  directionLo := (1170955252094239443/781250000000000000)
  directionHi := (29976454453612529741/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree010.table
  base := (23858273437231444150064780211272251671071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-1274767943286241985824738800786000000000000)
      constant := (7356029872298862185273865147752510532410999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree010.table
  base := (23810422263730614903175931677022558734859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-55744541346775969407517899139777953500000000000)
      constant := (321285899947700038713568350258740955307206540451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1170955252094239443/781250000000000000)
  centralHi := (29976454453612529741/20000000000000000000)
  directionLo := (3949744677071409353/2500000000000000000)
  directionHi := (157989787082856374121/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree011.table
  base := (3930418817378816205718202389603388390859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-1401686682763378603401929746731000000000000)
      constant := (7340034359239345470717106491867738190275855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree011.table
  base := (19610710171294512977880716143997632973041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (9029332)
      previous := (4514666)
      next := (4514666)
      square := (44120714397496455280722748838510000000000000)
      linear := (-506567099896576341507255580230297250000000000)
      constant := (2650430345147991730024885516658206457239758369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3949744677071409353/2500000000000000000)
  centralHi := (157989787082856374121/100000000000000000000)
  directionLo := (165701086613018080971/100000000000000000000)
  directionHi := (41425271653254520243/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree012.table
  base := (16153309143225521545463701496536639447749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-1528605422240515220979120692676000000000000)
      constant := (7509488615635369814782902197336692066669581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree012.table
  base := (16117198929028540558712243315577556365263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-66844696828195505237237951275953981000000000000)
      constant := (328216443994858352944150096625269686365887974407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165701086613018080971/100000000000000000000)
  centralHi := (41425271653254520243/25000000000000000000)
  directionLo := (173069140481437501607/100000000000000000000)
  directionHi := (21633642560179687701/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree013.table
  base := (13201426749569196474126745046669597661289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (723183700724425171380005390000000000000)
      linear := (-9796000956909182476664565909000000000000)
      constant := (46374375844449556320611069350544597661289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree013.table
  base := (658489472592774145238510369273854519199/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (3232394)
      previous := (1616197)
      next := (1616197)
      square := (15794693615671807955525007720295000000000000)
      linear := (-214185723576642819976621234745686375000000000)
      constant := (1013748967303832924430613017746765326125065190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173069140481437501607/100000000000000000000)
  centralHi := (21633642560179687701/12500000000000000000)
  directionLo := (22517009081064758099/12500000000000000000)
  directionHi := (180136072648518064793/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree014.table
  base := (10684242292510956053283771445681138693807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-1782442901194788456133502584566000000000000)
      constant := (8304414485802169771259125335771612439253383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree014.table
  base := (10656491758890951620909440761673195415887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-77944852309615041066958003412130008500000000000)
      constant := (363167472618421672029673662550824194443219847943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22517009081064758099/12500000000000000000)
  centralHi := (180136072648518064793/100000000000000000000)
  directionLo := (46734009264854972909/25000000000000000000)
  directionHi := (186936037059419891637/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree015.table
  base := (1064908198118164047176265402095795831307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-954680820335962536855346765255500000000000)
      constant := (4448491339142563308988399465172695481963532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree015.table
  base := (4247468006410388652947839786696215670327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-41747465025162404490909014740109011125000000000)
      constant := (194584673767034032089770719269494097600142323103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46734009264854972909/25000000000000000000)
  centralHi := (186936037059419891637/100000000000000000000)
  directionLo := (48374295365494366681/25000000000000000000)
  directionHi := (7739887258479098669/4000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree016.table
  base := (6643559903772071398445432375434608925057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-2036280380149061691287884476456000000000000)
      constant := (9604337788956912764214089314584448908334633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree016.table
  base := (6622257644641880799856031483305139648851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-89045007791034576896678055548306036000000000000)
      constant := (420188703852307333274923608041313121045246829739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48374295365494366681/25000000000000000000)
  centralHi := (7739887258479098669/4000000000000000000)
  directionLo := (390318417364746481/195312500000000000)
  directionHi := (199843029690750198273/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree017.table
  base := (1001572855267073867560908684832836776973/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-2163199119626198308865075422401000000000000)
      constant := (10418154713438687231390105209407622076542185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree017.table
  base := (4989243927670215864357520066972255694771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-94595085531744344811538081616394049750000000000)
      constant := (455862248844825175103592718557688021686743856619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390318417364746481/195312500000000000)
  centralHi := (199843029690750198273/100000000000000000000)
  directionLo := (205993479989602327141/100000000000000000000)
  directionHi := (102996739994801163571/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree018.table
  base := (3572966189355646131813638711606498465599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-2290117859103334926442266368346000000000000)
      constant := (11331806536986204368743971431736998240686231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree018.table
  base := (3556718942443311658070451705460686823217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-100145163272454112726398107684482063500000000000)
      constant := (495900782387492797754948093450416722098865160313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205993479989602327141/100000000000000000000)
  centralHi := (102996739994801163571/50000000000000000000)
  directionLo := (211965542200791030949/100000000000000000000)
  directionHi := (4239310844015820619/2000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree019.table
  base := (9012928179541782701803413314795275003/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-1208518299290235772009728657145500000000000)
      constant := (6169980145360199731093310736521088888864896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree019.table
  base := (143322342116131689928006737349298005753/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102245000000000000000000000000000000000000000
      center := (1513226)
      previous := (756613)
      next := (756613)
      square := (7394191748056885164774865110055000000000000)
      linear := (-146392300572249142162407387468933625000000000)
      constant := (748021582460769057763463995772327792950894776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211965542200791030949/100000000000000000000)
  centralHi := (4239310844015820619/2000000000000000000)
  directionLo := (10888694637412231211/5000000000000000000)
  directionHi := (217773892748244624221/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree020.table
  base := (1185320294816945555090310856044013470827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-2543955338057608161596648260236000000000000)
      constant := (13438293925488884420836396235141438276569763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree020.table
  base := (1173012921226586741255300219779489912279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-111245318753873648556118159820658091000000000000)
      constant := (588186062012446171031610270589311371782045770831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10888694637412231211/5000000000000000000)
  centralHi := (217773892748244624221/100000000000000000000)
  directionLo := (223431299609013109301/100000000000000000000)
  directionHi := (111715649804506554651/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree021.table
  base := (186175272903914150918682711777631616823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-2670874077534744779173839206181000000000000)
      constant := (14623288361218212203923729171003294743243087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree021.table
  base := (43871966911074367979758941095068402907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-58397698247291708235489092944373052375000000000)
      constant := (320045346216123376513046672160101010537538415446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223431299609013109301/100000000000000000000)
  centralHi := (111715649804506554651/50000000000000000000)
  directionLo := (228948952666792539511/100000000000000000000)
  directionHi := (28618619083349067439/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree022.table
  base := (-22097931857022579973569258827708917399/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-1398896408505940698375515076063000000000000)
      constant := (7946034591887907967027875162189625087353104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree022.table
  base := (-716402286816918160563053545781027569603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (9029332)
      previous := (4514666)
      next := (4514666)
      square := (44120714397496455280722748838510000000000000)
      linear := (-1011119621779282515585439768238298500000000000)
      constant := (5749256958411388051399422404314527757756090573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228948952666792539511/100000000000000000000)
  centralHi := (28618619083349067439/12500000000000000000)
  directionLo := (117168361994044535429/50000000000000000000)
  directionHi := (234336723988089070859/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree023.table
  base := (-94283214965553764723098119260473112003/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-1462355778244509007164110549035500000000000)
      constant := (8621141579940696622308949818104777852571944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree023.table
  base := (-1516559947782879906672388416454005900623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-127895551976002952300698238024922132250000000000)
      constant := (754791631823395872515308929898592582777263358553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117168361994044535429/50000000000000000000)
  centralHi := (234336723988089070859/100000000000000000000)
  directionLo := (239603375376304890757/100000000000000000000)
  directionHi := (119801687688152445379/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree024.table
  base := (-445887474106599010752530206837038858071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-3051630295966154631905412044016000000000000)
      constant := (18672000346146344281961615991646702164930005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree024.table
  base := (-447276916928839597631064032272529754479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-133445629716712720215558264093010146000000000000)
      constant := (817401160101506247492788500426628796986439366845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239603375376304890757/100000000000000000000)
  centralHi := (119801687688152445379/50000000000000000000)
  directionLo := (122378362848551681721/50000000000000000000)
  directionHi := (244756725697103363443/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree025.table
  base := (-2879230733035549908759554461909903295081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-3178549035443291249482602989961000000000000)
      constant := (20179635671230095576827489369259101343131311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree025.table
  base := (-2885236758652288165071137268086948923119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-138995707457422488130418290161098159750000000000)
      constant := (883419576305861176635008509614175600303268884409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122378362848551681721/50000000000000000000)
  centralHi := (244756725697103363443/100000000000000000000)
  directionLo := (390318417364746481/156250000000000000)
  directionHi := (249803787113437747841/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree026.table
  base := (-3465624227007627234898998028990293597369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (723183700724425171380005390000000000000)
      linear := (-19558980916688922290294638674000000000000)
      constant := (128780388691266336200072641742509706402631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree026.table
  base := (-3470812349770116672534524099859501532153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6464788)
      previous := (3232394)
      next := (3232394)
      square := (31589387231343615911050015440590000000000000)
      linear := (-855300504130960094942475243959681500000000000)
      constant := (5637811057784856369765428593402021582324024807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390318417364746481/156250000000000000)
  centralHi := (249803787113437747841/100000000000000000000)
  directionLo := (254750877012159383247/100000000000000000000)
  directionHi := (15921929813259961453/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree027.table
  base := (-3994967337274426343306048763971480739393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-3432386514397564484636984881851000000000000)
      constant := (23423677335992631321335840919497694755042583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree027.table
  base := (-199972285467332704406497903091085460437/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-75047931469421011980069171148637093625000000000)
      constant := (512732938367714763098362625607842023334324621070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254750877012159383247/100000000000000000000)
  centralHi := (15921929813259961453/6250000000000000000)
  directionLo := (25960371072215625241/10000000000000000000)
  directionHi := (259603710722156252411/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree028.table
  base := (-4472492749443230109866575473752801243211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-3559305253874701102214175827796000000000000)
      constant := (25158126288868326281373470935933776589897341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree028.table
  base := (-4476355993514755065464106973871954775437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-155645940679551791874998368365362201000000000000)
      constant := (1101408471940149946877123373566476965118749052107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25960371072215625241/10000000000000000000)
  centralHi := (259603710722156252411/100000000000000000000)
  directionLo := (132183739452855560237/50000000000000000000)
  directionHi := (10574699156228444819/4000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree029.table
  base := (-2451258533216285999326308751813519913833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-1843111996675918859895683386870500000000000)
      constant := (13483251520778931771248495927218952634562223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree029.table
  base := (-4905847775974296706659549907983142684699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-161196018420261559789858394433450214750000000000)
      constant := (1180586077633642436474620831718479016506540543789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132183739452855560237/50000000000000000000)
  centralHi := (10574699156228444819/4000000000000000000)
  directionLo := (269046912610440938569/100000000000000000000)
  directionHi := (26904691261044093857/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree030.table
  base := (-5288604587749315885891471686031510168001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-3813142732828974337368557719686000000000000)
      constant := (28848205227444583109623990510328174781607831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree030.table
  base := (-5291474711056333173105842628762360959937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-166746096160971327704718420501538228500000000000)
      constant := (1262972460423359917706019561346897627012369631607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269046912610440938569/100000000000000000000)
  centralHi := (26904691261044093857/10000000000000000000)
  directionLo := (273646338304496361141/100000000000000000000)
  directionHi := (136823169152248180571/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree031.table
  base := (-704212642875527851694353857555055166337/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-1970030736153055477472874332815500000000000)
      constant := (15401367500662133183330625406866720207556188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree031.table
  base := (-5636173245697668179964959028928148767359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-172296173901681095619578446569626242250000000000)
      constant := (1348545943196671128170463221760008088561303067049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273646338304496361141/100000000000000000000)
  centralHi := (136823169152248180571/50000000000000000000)
  directionLo := (278169724718035232653/100000000000000000000)
  directionHi := (139084862359017616327/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree032.table
  base := (-2970121796992417697317722571974507890817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-2033490105891623786261469805788000000000000)
      constant := (16414840266777409306006498997432308166451927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree032.table
  base := (-5942372000032993763540450912153450180783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-177846251642390863534438472637714256000000000000)
      constant := (1437288597663594579268367762526986201108393804313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278169724718035232653/100000000000000000000)
  centralHi := (139084862359017616327/50000000000000000000)
  directionLo := (141310361467194020633/50000000000000000000)
  directionHi := (282620722934388041267/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree033.table
  base := (-3105124766444647021873329864248925979781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-2096949475630192095050065278760500000000000)
      constant := (17464350425527377057804788358141869009417011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree033.table
  base := (-6212081348006276495713110899201742973579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (9029332)
      previous := (4514666)
      next := (4514666)
      square := (44120714397496455280722748838510000000000000)
      linear := (-1515672143661988689663623956246299750000000000)
      constant := (12637897380700434948372597315130683667612418789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141310361467194020633/50000000000000000000)
  centralHi := (282620722934388041267/100000000000000000000)
  directionLo := (287002700883118449539/100000000000000000000)
  directionHi := (14350135044155922477/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree034.table
  base := (-3222695419350358866907318118193560311277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-2160408845368760403838660751733000000000000)
      constant := (18549756703137962885513232831911038307394187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree034.table
  base := (-6446966862475020362139559030671561422403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-188946407123810399364158524773890283500000000000)
      constant := (1624224603993075197884640866992605663279604460133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287002700883118449539/100000000000000000000)
  centralHi := (14350135044155922477/5000000000000000000)
  directionLo := (291318773161726377499/100000000000000000000)
  directionHi := (116527509264690551/40000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree035.table
  base := (-830881757491220981789327594415201832099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-2223868215107328712627256224705500000000000)
      constant := (19670941936260015901721174124328761061501076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree035.table
  base := (-3324204797261148207403655699126904313683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-97248242432260083639509275420989148625000000000)
      constant := (861197732703276754881971033717285306214251926213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291318773161726377499/100000000000000000000)
  centralHi := (116527509264690551/40000000000000000)
  directionLo := (9236619591772059077/3125000000000000000)
  directionHi := (59114365387341178093/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree036.table
  base := (-6816390033674807363490431246881877224117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-4574655169691794042831703395356000000000000)
      constant := (41655617758317448872914019235282962749124227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree036.table
  base := (-170438889941727157581126530655813902849/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-100023281302614967596939288455033155500000000000)
      constant := (911844853518048457243400127510672796972126568780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9236619591772059077/3125000000000000000)
  centralHi := (59114365387341178093/20000000000000000000)
  directionLo := (299764544536125297409/100000000000000000000)
  directionHi := (29976454453612529741/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree037.table
  base := (-6954354700418675981488578500621036633063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-4701573909168930660408894341301000000000000)
      constant := (44040553509726577066736718300263919809012353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree037.table
  base := (-434709791038710042631799068062821467319/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-102798320172969851554369301489077162375000000000)
      constant := (964050151361155931013578373149407162786968154872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299764544536125297409/100000000000000000000)
  centralHi := (29976454453612529741/10000000000000000000)
  directionLo := (303899423236042479951/100000000000000000000)
  directionHi := (18993713952252654997/6250000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree038.table
  base := (-882717838706230576316168660513490428339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-2414246324323033638993042643623000000000000)
      constant := (23248278415491932401217608489940630470442836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree038.table
  base := (-3531301907738203527036224828503409028669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102245000000000000000000000000000000000000000
      center := (1513226)
      previous := (756613)
      next := (756613)
      square := (7394191748056885164774865110055000000000000)
      linear := (-292446977959348297816618599787039250000000000)
      constant := (2819420239483691078736405237289183023147747619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303899423236042479951/100000000000000000000)
  centralHi := (18993713952252654997/6250000000000000000)
  directionLo := (38497349081918920051/12500000000000000000)
  directionHi := (307978792655351360409/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree039.table
  base := (-1784803779073383594300761650547972489759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361591850362212585690002695000000000000)
      linear := (-14660980438234331051962355719500000000000)
      constant := (145039988176943638194129449900341555020482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree039.table
  base := (-1427991001006037530891523317869187914829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6464788)
      previous := (3232394)
      next := (3232394)
      square := (31589387231343615911050015440590000000000000)
      linear := (-1282229561108634549931708018427990250000000000)
      constant := (12699693376847271381186988451519215818149272255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38497349081918920051/12500000000000000000)
  centralHi := (307978792655351360409/100000000000000000000)
  directionLo := (39000603762893957869/12500000000000000000)
  directionHi := (312004830103151662953/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree040.table
  base := (-7187322228586308569634554687691095793757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-5082330127600340513140467179136000000000000)
      constant := (51621338026103852592585224124220204810855067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree040.table
  base := (-1437591565843927778218654041223362338353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-222246873568069006853318681182418366000000000000)
      constant := (2259976563601189596617972288220145679195150202915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39000603762893957869/12500000000000000000)
  centralHi := (312004830103151662953/100000000000000000000)
  directionLo := (315979574165712748241/100000000000000000000)
  directionHi := (157989787082856374121/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree041.table
  base := (-3603261236829948445338789125275925731643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-2604624433538738565358829062540500000000000)
      constant := (27144972711844655565780675528807306051352333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree041.table
  base := (-7207068376428960872408894743668401576829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-227796951308778774768178707250506379750000000000)
      constant := (2376803194764183127045562198206159649814295484219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315979574165712748241/100000000000000000000)
  centralHi := (157989787082856374121/50000000000000000000)
  directionLo := (19994058548357109409/6250000000000000000)
  directionHi := (63980987354742750109/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree042.table
  base := (-899649748635754000460585024826457125341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-2668083803277306874147424535513000000000000)
      constant := (28514636807656851253218775867537064983269484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree042.table
  base := (-1799416690808157005140028763765414855033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-116673514524744271341519366659297196750000000000)
      constant := (1248362634060893154695397191874440764195823592126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19994058548357109409/6250000000000000000)
  centralHi := (63980987354742750109/20000000000000000000)
  directionLo := (161891356976246898543/50000000000000000000)
  directionHi := (323782713952493797087/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree043.table
  base := (-7159667520037313397401420686524132626743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-5463086346031750365872040016971000000000000)
      constant := (59839268733042857403615826490462296586080433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree043.table
  base := (-7160069989608630733795296859602220413101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-238897106790198310597898759386682407250000000000)
      constant := (2619740443551948620492653965003848097742559152011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161891356976246898543/50000000000000000000)
  centralHi := (323782713952493797087/100000000000000000000)
  directionLo := (163807297713419235243/50000000000000000000)
  directionHi := (327614595426838470487/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree044.table
  base := (-1418839419390811402632630009487413533109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-5590005085508886983449230962916000000000000)
      constant := (62719885817732362429010501117477135564522895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree044.table
  base := (-3547271289948430257929908396617705433739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 305045000000000000000000000000000000000000000
      center := (4514666)
      previous := (2257333)
      next := (2257333)
      square := (22060357198748227640361374419255000000000000)
      linear := (-1010112332772347431870904072127150500000000000)
      constant := (11346474249225001301736151811181778346693017349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163807297713419235243/50000000000000000000)
  centralHi := (327614595426838470487/100000000000000000000)
  directionLo := (331402173226036161943/100000000000000000000)
  directionHi := (41425271653254520243/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree045.table
  base := (-350050444158476467769306130825882580951/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-2858461912493011800513210954430500000000000)
      constant := (32835543661889447771687614316737695938192810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree045.table
  base := (-13674424606205885645432423135057688993/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-124998631135808923213809405761429217375000000000)
      constant := (1437521305981759401377398410945962501175498277488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331402173226036161943/100000000000000000000)
  centralHi := (41425271653254520243/12500000000000000000)
  directionLo := (20946684338344978997/6250000000000000000)
  directionHi := (335146949413519663953/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree046.table
  base := (-6880288512199181312001474585565757475989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-5843842564463160218603612854806000000000000)
      constant := (68692841879118345546649647022042886986557859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree046.table
  base := (-6880542958639515849027890453977445837787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-255547340012327614342478837590946448500000000000)
      constant := (3007326612409416705624496168754522904801526802957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20946684338344978997/6250000000000000000)
  centralHi := (335146949413519663953/100000000000000000000)
  directionLo := (67770068609508412597/20000000000000000000)
  directionHi := (169425171523771031493/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree047.table
  base := (-6732191177403960353847297373121113323701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-5970761303940296836180803800751000000000000)
      constant := (71785123256072712316262118833446406848294531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree047.table
  base := (-3366204744481135419854858058076921486983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-130548708876518691128669431829517231125000000000)
      constant := (1571348815561630683748530950005021146545672902513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67770068609508412597/20000000000000000000)
  centralHi := (169425171523771031493/50000000000000000000)
  directionLo := (342513696464368511801/100000000000000000000)
  directionHi := (171256848232184255901/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree048.table
  base := (-819605836264382343277132596641831193981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3048840021708716726878997373348000000000000)
      constant := (37473954758263512179689023836254122112868844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree048.table
  base := (-819629246169042458800620441167937795903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-133323747746873575086099444863561238000000000000)
      constant := (1640577357981582197223829641316138455976720874532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342513696464368511801/100000000000000000000)
  centralHi := (171256848232184255901/50000000000000000000)
  directionLo := (173069140481437501607/50000000000000000000)
  directionHi := (69227656192575000643/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree049.table
  base := (-3177181842065605971950922010592563525177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3112299391447285035667592846320500000000000)
      constant := (39090591150684647692068870574207794264245087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree049.table
  base := (-6354524317752872289275235036293761768151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-272197573234456918087058915795210489750000000000)
      constant := (3422697070269264756618613981744457409599899452561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173069140481437501607/50000000000000000000)
  centralHi := (69227656192575000643/20000000000000000000)
  directionLo := (349725301958812846977/100000000000000000000)
  directionHi := (174862650979406423489/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree050.table
  base := (-6124833113208199355273102101535547760809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-6351517522371706688912376638586000000000000)
      constant := (81484926239414798670526423368827992428423279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree050.table
  base := (-122499417433793182052008535800826161953/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-138873825487583343000959470931649251750000000000)
      constant := (1783662013580953514717710822517054671457738504575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349725301958812846977/100000000000000000000)
  centralHi := (174862650979406423489/50000000000000000000)
  directionLo := (353275903667985051583/100000000000000000000)
  directionHi := (5519935994812266431/1562500000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree051.table
  base := (-2934165581243107034975038257752626872959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3239218130924421653244783792265500000000000)
      constant := (42429564227687420793199221260011243558469929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree051.table
  base := (-1467112321496656048440289859241871240121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-141648864357938226958389483965693258625000000000)
      constant := (1857517514075223862992661555007204052735116564462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353275903667985051583/100000000000000000000)
  centralHi := (5519935994812266431/1562500000000000000)
  directionLo := (178395586684957037857/50000000000000000000)
  directionHi := (71358234673982815143/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree052.table
  base := (-5584921673714850639201621927776357451797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (723183700724425171380005390000000000000)
      linear := (-39084940836248401917554784204000000000000)
      constant := (522507563076886051198753622270223642548203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree052.table
  base := (-1396255736533420638073939574550495827183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (3232394)
      previous := (1616197)
      next := (1616197)
      square := (15794693615671807955525007720295000000000000)
      linear := (-854579309043154502460470396448149500000000000)
      constant := (11437365696205795814239977485958049521045638754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178395586684957037857/50000000000000000000)
  centralHi := (71358234673982815143/20000000000000000000)
  directionLo := (22517009081064758099/6250000000000000000)
  directionHi := (72054429059407225917/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree053.table
  base := (-2637329083400311878155653369437251047209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3366136870401558270821974738210500000000000)
      constant := (45909433154203650442967129620037542073021679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree053.table
  base := (-2637372489794276038365671998998378703281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-147198942098647994873249510033781272375000000000)
      constant := (2009853683235809794927484656195191878021518815991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22517009081064758099/6250000000000000000)
  centralHi := (72054429059407225917/20000000000000000000)
  directionLo := (363719804188852687863/100000000000000000000)
  directionHi := (45464975523606585983/12500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree054.table
  base := (-4937585525936971780519826743430270195641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-6859192480280253159221140422366000000000000)
      constant := (95404385315186825203721456159951784336936671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree054.table
  base := (-987531986611838458730624404408521583153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-299947961938005757661359046135650558500000000000)
      constant := (4176667982764866725677244023445439442292468266915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363719804188852687863/100000000000000000000)
  centralHi := (45464975523606585983/12500000000000000000)
  directionLo := (367135088545655045163/100000000000000000000)
  directionHi := (91783772136413761291/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree055.table
  base := (-914748281365330314895522074302692101431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-6986111219757389776798331368311000000000000)
      constant := (99060328816518549696163030518616100174290805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree055.table
  base := (-457380517209031829270112342471608069989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 305045000000000000000000000000000000000000000
      center := (4514666)
      previous := (2257333)
      next := (2257333)
      square := (22060357198748227640361374419255000000000000)
      linear := (-1262388593713700518909996166131151125000000000)
      constant := (17920294125460842034746160480218249156133955495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367135088545655045163/100000000000000000000)
  centralHi := (91783772136413761291/25000000000000000000)
  directionLo := (92629723403072204489/25000000000000000000)
  directionHi := (370518893612288817957/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree056.table
  base := (-1045789352954680476557509130731063379409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3556514979617263197187761157128000000000000)
      constant := (51393345735802741715729656641000900577759758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree056.table
  base := (-836642409922708764618857830113183022889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-311048117419425293491079098271826586000000000000)
      constant := (4499836721811459146438591848154111457758721824395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92629723403072204489/25000000000000000000)
  centralHi := (370518893612288817957/100000000000000000000)
  directionLo := (373872074118839783273/100000000000000000000)
  directionHi := (186936037059419891637/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree057.table
  base := (-1882930035893749635778209372500196755411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3619974349355831505976356630100500000000000)
      constant := (53291734398364933460911800230304404248335541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree057.table
  base := (-3765906882146936996758756656824147397619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3026452)
      previous := (1513226)
      next := (1513226)
      square := (14788383496113770329549730220110000000000000)
      linear := (-877003310692894906941659624210289750000000000)
      constant := (12925330800121313847249325072392809814553589069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373872074118839783273/100000000000000000000)
  centralHi := (186936037059419891637/50000000000000000000)
  directionLo := (377195446802015171921/100000000000000000000)
  directionHi := (188597723401007585961/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree058.table
  base := (-3321871666977067365370437262830769564367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-7366867438188799629529904206146000000000000)
      constant := (110450657026530450022815480096397099943621977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree058.table
  base := (-3321911765744490094011323452347411190521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-322148272900844829320799150408002613500000000000)
      constant := (4835334106343492109845202797746536993890728021631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377195446802015171921/100000000000000000000)
  centralHi := (188597723401007585961/50000000000000000000)
  directionLo := (76097958545658893823/20000000000000000000)
  directionHi := (95122448182073617279/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree059.table
  base := (-2851210913575199508878889543567055180163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-7493786177665936247107095152091000000000000)
      constant := (114388252997971499043151003417418042674552453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree059.table
  base := (-570249051670506052535120482843724377383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-327698350641554597235659176476090627250000000000)
      constant := (5007705647314141135174831121432137268453133034565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76097958545658893823/20000000000000000000)
  centralHi := (95122448182073617279/25000000000000000000)
  directionLo := (2398474121484821719/625000000000000000)
  directionHi := (383755859437571475041/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree060.table
  base := (-9194896633838787442227639925310015087/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3810352458571536432342143049018000000000000)
      constant := (59198127026621976528290726942090693753638016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree060.table
  base := (-2353922950726487586122591789887677579559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-333248428382264365150519202544178641000000000000)
      constant := (5183158926663397212737169193109085995979390881249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2398474121484821719/625000000000000000)
  centralHi := (383755859437571475041/100000000000000000000)
  directionLo := (386994362923954933449/100000000000000000000)
  directionHi := (7739887258479098669/2000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree061.table
  base := (-457483189810692778092965812327473592993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3873811828310104741130738521990500000000000)
      constant := (61237328979235742939281801673784751425568366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree061.table
  base := (-114372371520762891946140044523728211737/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-169399253061487066532689614306133327375000000000)
      constant := (2680846923837536725068794366163959623735516721256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386994362923954933449/100000000000000000000)
  centralHi := (7739887258479098669/2000000000000000000)
  directionLo := (97551497367149102973/25000000000000000000)
  directionHi := (390205989468596411893/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree062.table
  base := (-159917461144097827919180921140366962157/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-3937271198048673049919333994963000000000000)
      constant := (63311731417809183508511088180638861933581868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree062.table
  base := (-639680625782694396662508598280726146071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-172174291931841950490119627340177334250000000000)
      constant := (2771655164527342334241835995791618088839451877681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97551497367149102973/25000000000000000000)
  centralHi := (390205989468596411893/100000000000000000000)
  directionLo := (393391397337835799031/100000000000000000000)
  directionHi := (49173924667229474879/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree063.table
  base := (-175530918172414922662494762099637376297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-4000730567787241358707929467935500000000000)
      constant := (65421333552715410560102763114300260066811614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree063.table
  base := (-702142131059341289692011021820667622479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-349898661604393668895099280748442682250000000000)
      constant := (5728008302454175783507771676314607251438629121369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393391397337835799031/100000000000000000000)
  centralHi := (49173924667229474879/12500000000000000000)
  directionLo := (396551218358566680711/100000000000000000000)
  directionHi := (49568902294820835089/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree064.table
  base := (-98292569642016753521007708935572309873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-8128379875051619334993049881816000000000000)
      constant := (135132269439604572347878789097253888279631463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree064.table
  base := (-98308368723330352783865941832080510193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-355448739345103436809959306816530696000000000000)
      constant := (5915787710397271643298996489859111142618589866823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396551218358566680711/100000000000000000000)
  centralHi := (49568902294820835089/12500000000000000000)
  directionLo := (79937211876300079309/20000000000000000000)
  directionHi := (199843029690750198273/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree065.table
  base := (66518375968864849405745466221977486199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361591850362212585690002695000000000000)
      linear := (-24423960398014070865592428484500000000000)
      constant := (412699019883642577723848748443325409944796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree065.table
  base := (532133486613803349678028897189897844423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6464788)
      previous := (3232394)
      next := (3232394)
      square := (31589387231343615911050015440590000000000000)
      linear := (-2136087675063983459910173567364607750000000000)
      constant := (36134014819762928404031998286010408607429741063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79937211876300079309/20000000000000000000)
  centralHi := (199843029690750198273/50000000000000000000)
  directionLo := (402796503641926974249/100000000000000000000)
  directionHi := (1611186014567707897/400000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree066.table
  base := (297297373917511871794150112905237029937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-4191108677002946285073715886853000000000000)
      constant := (71961332004172625039189813637223720116118706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree066.table
  base := (74323620346854294831172547514182760523/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 305045000000000000000000000000000000000000000
      center := (4514666)
      previous := (2257333)
      next := (2257333)
      square := (22060357198748227640361374419255000000000000)
      linear := (-1514664854655053605949088260135151750000000000)
      constant := (26035498529798623002227612218129802317668981656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402796503641926974249/100000000000000000000)
  centralHi := (1611186014567707897/400000000000000000)
  directionLo := (405883112026614774883/100000000000000000000)
  directionHi := (101470778006653693721/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree067.table
  base := (1872830211600903720042202048833283514943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-8509136093483029187724622719651000000000000)
      constant := (148423454511281804084258389630151699914025367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree067.table
  base := (936410156130728070510756864594484226277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-186049486283616370277269692510397368625000000000)
      constant := (3248807047594605336653953604025056574869816702653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405883112026614774883/100000000000000000000)
  centralHi := (101470778006653693721/25000000000000000000)
  directionLo := (408946424254642613437/100000000000000000000)
  directionHi := (204473212127321306719/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree068.table
  base := (516613042807694576394641157889959514589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-8636054832960165805301813665596000000000000)
      constant := (152994639563366505818891207939255015789827705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree068.table
  base := (516611349060295164536488829650922865737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-377649050307942508469399411088882751000000000000)
      constant := (6697718828672932545653445333674502957510027922965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408946424254642613437/100000000000000000000)
  centralHi := (204473212127321306719/50000000000000000000)
  directionLo := (205993479989602327141/50000000000000000000)
  directionHi := (411986959979204654283/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree069.table
  base := (829972796167692408676931359809762369069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-4381486786218651211439502305770500000000000)
      constant := (78818109301902314880055911714086137180745322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree069.table
  base := (132795357628733534716070777315912819381/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-383199128048652276384259437156970764750000000000)
      constant := (6900904820420010955392728878820960324402474172725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205993479989602327141/50000000000000000000)
  centralHi := (411986959979204654283/100000000000000000000)
  directionLo := (415005219816757734419/100000000000000000000)
  directionHi := (20750260990837886721/5000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree070.table
  base := (2041652664704958162241000729586771980763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-4444946155957219520228097778743000000000000)
      constant := (81174095580197662292217080367403914464748947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree070.table
  base := (4083299133893876750172078046713206826113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-388749205789362044299119463225058778500000000000)
      constant := (7107172050021788542519214772368113994484523690057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415005219816757734419/100000000000000000000)
  centralHi := (20750260990837886721/5000000000000000000)
  directionLo := (83600337261856554219/20000000000000000000)
  directionHi := (52250210788660346387/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree071.table
  base := (4873305295232045277318556096402434916917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-9016811051391575658033386503431000000000000)
      constant := (167130556835477556654956026118929886500958973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree071.table
  base := (38986399976604287991810291313425826301/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-394299283530071812213979489293146792250000000000)
      constant := (7316520500294588776263153527341018318573752848625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83600337261856554219/20000000000000000000)
  centralHi := (52250210788660346387/12500000000000000000)
  directionLo := (52622103103112221451/12500000000000000000)
  directionHi := (420976824824897771609/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree072.table
  base := (5689889100282030915885905902005177904679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-9143729790868712275610577449376000000000000)
      constant := (171983315294117809749108398877670875065890751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree072.table
  base := (5689884570076087003591127332173473570133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-399849361270781580128839515361234806000000000000)
      constant := (7528950156768135074665795130875464724833869547837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52622103103112221451/12500000000000000000)
  centralHi := (420976824824897771609/100000000000000000000)
  directionLo := (423931084401582061899/100000000000000000000)
  directionHi := (4239310844015820619/1000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree073.table
  base := (1306611015022449932613554643072281597859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-9270648530345848893187768395321000000000000)
      constant := (176906466254179435482358628086385952950190855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree073.table
  base := (408315700126469463117473610523208323563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-202699719505745674021849770714661409875000000000)
      constant := (3872230503627771635313633280375880461401756654856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423931084401582061899/100000000000000000000)
  centralHi := (4239310844015820619/1000000000000000000)
  directionLo := (426864898538343069127/100000000000000000000)
  directionHi := (53358112317292883641/12500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree074.table
  base := (3701400906634940993620677023293532051849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-4698783634911492755382479670633000000000000)
      constant := (90950004738985953676931229935392356916762481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree074.table
  base := (7402798502387322711116015028963296102141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-410949516752201115958559567497410833500000000000)
      constant := (7963053041491793555541620171663792735278107952549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426864898538343069127/100000000000000000000)
  centralHi := (53358112317292883641/12500000000000000000)
  directionLo := (214889342968886286249/50000000000000000000)
  directionHi := (429778685937772572499/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree075.table
  base := (414956406486800711802173035960686847123/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-4762243004650061064171075143605500000000000)
      constant := (93481972382613514478185257756771998271637870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree075.table
  base := (829912529979469559615115538277364542491/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-208249797246455441936709796782749423625000000000)
      constant := (4092363125414853740390249629410884472655407968495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214889342968886286249/50000000000000000000)
  centralHi := (429778685937772572499/100000000000000000000)
  directionLo := (216336425601796877009/50000000000000000000)
  directionHi := (432672851203593754019/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree076.table
  base := (368881321038454340820264469748110142899/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-9651404748777258745919341233156000000000000)
      constant := (192098271947189970636647290642931765353748275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree076.table
  base := (9222030607389926093347987185369372495101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3026452)
      previous := (1513226)
      next := (1513226)
      square := (14788383496113770329549730220110000000000000)
      linear := (-1169112665467093218250082048846501000000000000)
      constant := (23294960188321962353095916694106506173152320349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216336425601796877009/50000000000000000000)
  centralHi := (432672851203593754019/100000000000000000000)
  directionLo := (10888694637412231211/2500000000000000000)
  directionHi := (435547785496489248441/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree077.table
  base := (10171515660445594473402138181691199427159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-9778323488254395363496532179101000000000000)
      constant := (197302990881647178252631140208364687703189871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree077.table
  base := (2034302718738343140719833424879670975763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (9029332)
      previous := (4514666)
      next := (4514666)
      square := (44120714397496455280722748838510000000000000)
      linear := (-3533882231192813385976360708278304750000000000)
      constant := (71382778238159399952454738396946230724989124335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10888694637412231211/2500000000000000000)
  centralHi := (435547785496489248441/100000000000000000000)
  directionLo := (438403867151219868429/100000000000000000000)
  directionHi := (43840386715121986843/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree078.table
  base := (11147575323976643526423819979429412342567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (723183700724425171380005390000000000000)
      linear := (-58610900755807881544814929734000000000000)
      constant := (1198686990820957458735374633258929412342567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree078.table
  base := (11147573558071033075986406493441409204391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6464788)
      previous := (3232394)
      next := (3232394)
      square := (31589387231343615911050015440590000000000000)
      linear := (-2563016732041657914899406341832916500000000000)
      constant := (52474750663649577335517292770635640414207003271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438403867151219868429/100000000000000000000)
  centralHi := (43840386715121986843/10000000000000000000)
  directionLo := (110310365564447599501/25000000000000000000)
  directionHi := (88248292451558079601/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree079.table
  base := (607510570939401172462394157952019496167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-5016080483604334299325457035495500000000000)
      constant := (103961801773725665980332045638926850448522230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree079.table
  base := (12150209910113242702277344285841907876887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-438699905455749955532859697837850902250000000000)
      constant := (9102230709644208549609491801561967847994168376943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110310365564447599501/25000000000000000000)
  centralHi := (88248292451558079601/20000000000000000000)
  directionLo := (55507615651148730649/12500000000000000000)
  directionHi := (444060925209189845193/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree080.table
  base := (52717693764045220059963524963317311341/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-5079539853342902608114052508468000000000000)
      constant := (106669748546310989008222586262290078202078625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree080.table
  base := (3294855538061572080339477688333088992283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-222124991598229861723859861952969458000000000000)
      constant := (4669654852803228065367840006985104764171906838374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55507615651148730649/12500000000000000000)
  centralHi := (444060925209189845193/100000000000000000000)
  directionLo := (223431299609013109301/50000000000000000000)
  directionHi := (446862599218026218603/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree081.table
  base := (7117605482950180610930644408642278041859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-5142999223081470916902647981440500000000000)
      constant := (109412891006235826615159394483534482489074171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree081.table
  base := (7117604932557859682360600281433925703469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-224900030468584745681289874987013464875000000000)
      constant := (4789734923473904718219084271589518081470989516741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223431299609013109301/50000000000000000000)
  centralHi := (446862599218026218603/100000000000000000000)
  directionLo := (449646816804187946113/100000000000000000000)
  directionHi := (224823408402093973057/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree082.table
  base := (15317573635387697153835240875640877950471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-10412917185640078451382486908826000000000000)
      constant := (224382458246486950961476907418162808373629599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree082.table
  base := (7658786347635185779043856083567691558319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-227675069338939629638719888021057471750000000000)
      constant := (4911355565529530257445302848945272696592434548391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449646816804187946113/100000000000000000000)
  centralHi := (224823408402093973057/50000000000000000000)
  directionLo := (452413900255493459123/100000000000000000000)
  directionHi := (113103475063873364781/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree083.table
  base := (16426511147603291966137841180206307420757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-10539835925117215068959677854771000000000000)
      constant := (230009525743651837687152570414029740954107933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree083.table
  base := (2053313793099020187990312042474095975317/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-230450108209294513596149901055101478625000000000)
      constant := (5034516777870475779871483051152699038764671338852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452413900255493459123/100000000000000000000)
  centralHi := (113103475063873364781/25000000000000000000)
  directionLo := (56895520257891928681/12500000000000000000)
  directionHi := (455164162063135429449/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree084.table
  base := (2195252906005657396080699194494514814249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-5333377332297175843268434400358000000000000)
      constant := (117853492230477747295257453550545292014432324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree084.table
  base := (17562022562561904127617896560861712335119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-466450294159298795107159828178290971000000000000)
      constant := (10318437119139698397167024395911684178025246283591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56895520257891928681/12500000000000000000)
  centralHi := (455164162063135429449/100000000000000000000)
  directionLo := (457897905333585079023/100000000000000000000)
  directionHi := (28618619083349067439/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree085.table
  base := (1872410972214106380260912080760032167859/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-5396836702035744152057029873330500000000000)
      constant := (120737417181067581631767636366670664681840855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree085.table
  base := (18724109136902128143639601470218591214409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-472000371900008563022019854246378984750000000000)
      constant := (10570921819692679094838021879695260040229072820401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457897905333585079023/100000000000000000000)
  centralHi := (28618619083349067439/6250000000000000000)
  directionLo := (460615424178493475511/100000000000000000000)
  directionHi := (57576928022311684439/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree086.table
  base := (19912770388979552436521039249928363139601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-10920592143548624921691250692606000000000000)
      constant := (247313075416616858776288919467981393370592569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree086.table
  base := (19912769889379067097316172629445606576783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-477550449640718330936879880314466998500000000000)
      constant := (10826487656082679708182359529345704461127547439687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460615424178493475511/100000000000000000000)
  centralHi := (57576928022311684439/12500000000000000000)
  directionLo := (231658502042004763607/50000000000000000000)
  directionHi := (92663400816801905443/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree087.table
  base := (21128005096028931727612823094534721635759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-11047510883025761539268441638551000000000000)
      constant := (253221707598622708053847966446770242956443271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree087.table
  base := (10564002334790306261332365994871038461051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-241550263690714049425869953191277506125000000000)
      constant := (5542567313599672332913249133315312233312995265539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231658502042004763607/50000000000000000000)
  centralHi := (92663400816801905443/20000000000000000000)
  directionLo := (58250365282603422969/12500000000000000000)
  directionHi := (466002922260827383753/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree088.table
  base := (22369813714685142906821001857690467445561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-11174429622502898156845632584496000000000000)
      constant := (259200730886418625164240687157957688998299809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree088.table
  base := (4473962670143218897755145725349621993031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (9029332)
      previous := (4514666)
      next := (4514666)
      square := (44120714397496455280722748838510000000000000)
      linear := (-4038434753075519560054544896286306000000000000)
      constant := (93775725058733007917114379633688950940864141395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58250365282603422969/12500000000000000000)
  centralHi := (466002922260827383753/100000000000000000000)
  directionLo := (117168361994044535429/25000000000000000000)
  directionHi := (468673447976178141717/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree089.table
  base := (23638196136519718335820716044352174701701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-11301348361980034774422823530441000000000000)
      constant := (265250145261680199076590180346881392524587469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree089.table
  base := (5909548956477048346610796795720391724149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-247100341431423817340729979259365519875000000000)
      constant := (5805835985007874849589390403530721039641156484522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117168361994044535429/25000000000000000000)
  centralHi := (468673447976178141717/100000000000000000000)
  directionLo := (117832210717222815161/25000000000000000000)
  directionHi := (94265768573778252129/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree090.table
  base := (6233288067529230586979276778095201449381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-5714133550728585696000007238193000000000000)
      constant := (135684975354479085231612507459959928089890778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree090.table
  base := (24933152005067830769497585917374015149871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-499750760603557402596319984586819053500000000000)
      constant := (11879562340261466294432715762208074015342446060519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117832210717222815161/25000000000000000000)
  centralHi := (94265768573778252129/20000000000000000000)
  directionLo := (473969361248569122361/100000000000000000000)
  directionHi := (236984680624284561181/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree091.table
  base := (26254682038407400559229824637868291628087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (723183700724425171380005390000000000000)
      linear := (-68373880715587621358445002499000000000000)
      constant := (1642367735001348038066682909203743291628087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree091.table
  base := (5250936362452032225212963132402302535099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6464788)
      previous := (3232394)
      next := (3232394)
      square := (31589387231343615911050015440590000000000000)
      linear := (-2989945789019332369888639116301225250000000000)
      constant := (71896649954338970153625677931602293377365797095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473969361248569122361/100000000000000000000)
  centralHi := (236984680624284561181/50000000000000000000)
  directionLo := (238297625189921503717/50000000000000000000)
  directionHi := (95319050075968601487/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree092.table
  base := (6900696344105054196113963457468795388373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-5841052290205722313577198184138000000000000)
      constant := (141910367384754527385703580526875452841270074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree092.table
  base := (27602785183484314295634978328257899868323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-510850916084976938426040036722995081000000000000)
      constant := (12424586475608748564166523878689078965656048666747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238297625189921503717/50000000000000000000)
  centralHi := (95319050075968601487/20000000000000000000)
  directionLo := (95841350150521956303/20000000000000000000)
  directionHi := (119801687688152445379/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree093.table
  base := (28977462229387486678649255659292444442591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-11809023319888581244731587314221000000000000)
      constant := (290151713362546107023342399418955298110797879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree093.table
  base := (1811091379050109939014999873671922977943/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-258200496912843353170450031395541547375000000000)
      constant := (6350860119919837540398997373612290220446905853416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95841350150521956303/20000000000000000000)
  centralHi := (119801687688152445379/25000000000000000000)
  directionLo := (48180409633908521231/10000000000000000000)
  directionHi := (481804096339085212311/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree094.table
  base := (30378712551146193164429356850300690363797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-11935942059365717862308778260166000000000000)
      constant := (296553082986537425302997792967432316671481693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree094.table
  base := (30378712410758440268238639937106395248821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-521951071566396474255760088859171108500000000000)
      constant := (12981935134640519626114093697596341181664723767069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48180409633908521231/10000000000000000000)
  centralHi := (481804096339085212311/100000000000000000000)
  directionLo := (484387514838451563453/100000000000000000000)
  directionHi := (242193757419225781727/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree095.table
  base := (31806536302790501909919359504870054634547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-12062860798842854479885969206111000000000000)
      constant := (303024843634907923608286162854414914233238443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree095.table
  base := (6361307236610899095517229041203886459429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3026452)
      previous := (1513226)
      next := (1513226)
      square := (14788383496113770329549730220110000000000000)
      linear := (-1461222020241291529558504473482712250000000000)
      constant := (36745792686228668160893693531586433050731818105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484387514838451563453/100000000000000000000)
  centralHi := (242193757419225781727/50000000000000000000)
  directionLo := (486957227909823474923/100000000000000000000)
  directionHi := (121739306977455868731/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree096.table
  base := (3326093345153524697969577791010825978681/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-6094889769159995548731580076028000000000000)
      constant := (154783497651058454448060469997212147951985445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree096.table
  base := (16630466674711318869497782100913376992051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-266525613523908005042740070497673568000000000000)
      constant := (6775804157432781918460582102389274878245872774539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486957227909823474923/100000000000000000000)
  centralHi := (121739306977455868731/25000000000000000000)
  directionLo := (122378362848551681721/25000000000000000000)
  directionHi := (97902690278841345377/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree097.table
  base := (17370951984878723407809301814367820152929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-6158349138898563857520175549000500000000000)
      constant := (158089768991748048641588231480780099105845001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree097.table
  base := (34741903882682424267272874462617048199637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-538601304788525778000340167063435149750000000000)
      constant := (13841066599850915070930006061142055041094197601693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122378362848551681721/25000000000000000000)
  centralHi := (97902690278841345377/20000000000000000000)
  directionLo := (123014098881519730459/25000000000000000000)
  directionHi := (492056395526078921837/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree098.table
  base := (36249447834187923343456353620934797628627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-12443617017274264332617542043946000000000000)
      constant := (322862471675112997674907611122093480799237963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree098.table
  base := (4531180969992848793976356587076875746863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-272075691264617772957600096565761581750000000000)
      constant := (7066803007257809515555343583805229943155511547228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123014098881519730459/25000000000000000000)
  centralHi := (492056395526078921837/100000000000000000000)
  directionLo := (61823283141897384027/12500000000000000000)
  directionHi := (494586265135179072217/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree099.table
  base := (302268520201835897816843390151602464301/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-12570535756751400950194732989891000000000000)
      constant := (329615796373655685073512875380123477058358625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree099.table
  base := (18891782480964787647400463683733448348233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 305045000000000000000000000000000000000000000
      center := (4514666)
      previous := (2257333)
      next := (2257333)
      square := (22060357198748227640361374419255000000000000)
      linear := (-2271493637479112867066364542147153625000000000)
      constant := (59624903135195835321453233653469150071371097097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61823283141897384027/12500000000000000000)
  centralHi := (494586265135179072217/100000000000000000000)
  directionLo := (99420651967810848583/20000000000000000000)
  directionHi := (124275814959763560729/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree100.table
  base := (19672127763190925189087078588731725830967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-6348727248114268783885961967918000000000000)
      constant := (168219756038167805396027032860170661665433423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree100.table
  base := (39344255472418427374410290781243491831919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-555251538010655081744920245267699191000000000000)
      constant := (14727928232336464812595119161212808009248999098791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99420651967810848583/20000000000000000000)
  centralHi := (124275814959763560729/25000000000000000000)
  directionLo := (499607574226875495681/100000000000000000000)
  directionHi := (249803787113437747841/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree101.table
  base := (1279109978867391947051991107846328246871/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-6412186617852837092674557440890500000000000)
      constant := (171666809390402811658776189226962909079539184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree101.table
  base := (40931519277756558086225050965280657702289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-560801615751364849659780271335787204750000000000)
      constant := (15029711035272050925683236775451688760316520401721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499607574226875495681/100000000000000000000)
  centralHi := (249803787113437747841/50000000000000000000)
  directionLo := (50209939803500216617/10000000000000000000)
  directionHi := (502099398035002166171/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree102.table
  base := (21272678202833865935705638956729825573761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-6475645987591405401463152913863000000000000)
      constant := (175149058242545408593829148443287090521965609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree102.table
  base := (10636339091614853305136009599750631493053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-283175846746037308787320148701937609250000000000)
      constant := (7667287483719685242877348345025599089585215255434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50209939803500216617/10000000000000000000)
  centralHi := (502099398035002166171/100000000000000000000)
  directionLo := (504578916314742748891/100000000000000000000)
  directionHi := (126144729078685687223/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree103.table
  base := (11046441690571766996025294524408902526117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-6539105357329973710251748386835500000000000)
      constant := (178666502593765100533969736692685146553827546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree103.table
  base := (4418576672887051655720844501109889002801/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-285950885616392192744750161735981616125000000000)
      constant := (7821260014383569262962951494847502986990084906445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504578916314742748891/100000000000000000000)
  centralHi := (126144729078685687223/25000000000000000000)
  directionLo := (101409261918546433189/20000000000000000000)
  directionHi := (253523154796366082973/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree104.table
  base := (22926375192676258453569148772711333021263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361591850362212585690002695000000000000)
      linear := (-39068430337683680586037537632000000000000)
      constant := (1078219777771383110227548322280711333021263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree104.table
  base := (11463187589218646434206565753852888403369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (3232394)
      previous := (1616197)
      next := (1616197)
      square := (15794693615671807955525007720295000000000000)
      linear := (-1708437422998503412438935945384767000000000000)
      constant := (47199840885193631093371875405375737786695122578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101409261918546433189/20000000000000000000)
  centralHi := (253523154796366082973/50000000000000000000)
  directionLo := (254750877012159383247/50000000000000000000)
  directionHi := (101900350804863753299/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree105.table
  base := (47546307267922745030906985122748444947523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-13332048193614220655657878665561000000000000)
      constant := (371613955581509602374548830481446362196131387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree105.table
  base := (11886576810913893394275219577135132593107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-291500963357101960659610187804069629875000000000)
      constant := (8133826769336990084864078276153612235529327071046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254750877012159383247/50000000000000000000)
  centralHi := (101900350804863753299/20000000000000000000)
  directionLo := (10238908430806597529/2000000000000000000)
  directionHi := (511945421540329876451/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree106.table
  base := (9853287480833984067945462080432461142271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-13458966933091357273235069611506000000000000)
      constant := (378860017270891630810202057794828929665218995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree106.table
  base := (49266437383492597506720384480839263115821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-588552004454913689234080401676227273500000000000)
      constant := (16584841987160505042131317645689999927734157930069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10238908430806597529/2000000000000000000)
  centralHi := (511945421540329876451/100000000000000000000)
  directionLo := (51437747998756193849/10000000000000000000)
  directionHi := (514377479987561938491/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree107.table
  base := (25506570394602461128263021773182091081237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-6792942836284246945406130278725500000000000)
      constant := (193088234977023657593172819514262210892729053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree107.table
  base := (12753285192896955850615638077904287602703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-297051041097811728574470213872157643625000000000)
      constant := (8452555782309801944132156852139893540344344123134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51437747998756193849/10000000000000000000)
  centralHi := (514377479987561938491/100000000000000000000)
  directionLo := (51679809326332011111/10000000000000000000)
  directionHi := (516798093263320111111/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree108.table
  base := (52786417418929890799521587323600587932369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-13712804412045630508389451503396000000000000)
      constant := (393563313630284117166058484250366499360570361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree108.table
  base := (6598302175490162545048076527731139294283/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-299826079968166612531900226906201650500000000000)
      constant := (8614231135510800536389304376068865135804677188748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51679809326332011111/10000000000000000000)
  centralHi := (516798093263320111111/100000000000000000000)
  directionLo := (519207421444312504821/100000000000000000000)
  directionHi := (259603710722156252411/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree109.table
  base := (2729313364495691979659735123647746685217/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-6919861575761383562983321224670500000000000)
      constant := (200510274149511100025938921012630129398016730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree109.table
  base := (13646566819282131776740870392798500779879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-302601118838521496489330239940245657375000000000)
      constant := (8777447053170829773916221024829238063674616124462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519207421444312504821/100000000000000000000)
  centralHi := (259603710722156252411/50000000000000000000)
  directionLo := (521605620910185907259/100000000000000000000)
  directionHi := (26080281045509295363/5000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree110.table
  base := (11282538079857545290100593308055263885517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-13966641890999903743543833395286000000000000)
      constant := (408548173959776695714193542958454197983261865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree110.table
  base := (28206345194198595923629485573038487360847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 305045000000000000000000000000000000000000000
      center := (4514666)
      previous := (2257333)
      next := (2257333)
      square := (22060357198748227640361374419255000000000000)
      linear := (-2523769898420465954105456636151154250000000000)
      constant := (73902508556029002386197584175167665934772914623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521605620910185907259/100000000000000000000)
  centralHi := (26080281045509295363/5000000000000000000)
  directionLo := (130998211115493195227/25000000000000000000)
  directionHi := (523992844461972780909/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree111.table
  base := (11653137348931187907084350645761599161111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-14093560630477040361121024341231000000000000)
      constant := (416146190612142745752717425205796426291138795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree111.table
  base := (5826568673538008471331663456325189722313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-308151196579231264404190266008333671125000000000)
      constant := (9108500581828175424756905371593588151668593009285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130998211115493195227/25000000000000000000)
  centralHi := (523992844461972780909/100000000000000000000)
  directionLo := (526369241435703410281/100000000000000000000)
  directionHi := (263184620717851705141/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree112.table
  base := (60145256324021632995000847796318079620779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-14220479369954176978698215287176000000000000)
      constant := (423814598255782883218300902475849755455911651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree112.table
  base := (60145256316121651922810511510807693403971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-621852470899172296723240558084755356000000000000)
      constant := (18552676385619220291929011302015284236592826875419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526369241435703410281/100000000000000000000)
  centralHi := (263184620717851705141/50000000000000000000)
  directionLo := (132183739452855560237/25000000000000000000)
  directionHi := (528734957811422240949/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree113.table
  base := (7756424891965468411948615292035629483007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-7173699054715656798137703116560500000000000)
      constant := (215776698445208194524878450176206023030512732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree113.table
  base := (62051399128996057021223385808608998158751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-627402548639882064638100584152843369750000000000)
      constant := (18891432736435624835298726505000899658725923510839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132183739452855560237/25000000000000000000)
  centralHi := (528734957811422240949/100000000000000000000)
  directionLo := (53109013631783360969/10000000000000000000)
  directionHi := (531090136317833609691/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree114.table
  base := (3999007198648993000160038558412524763271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-7237158424454225106926298589533000000000000)
      constant := (219681293257905157293816866504999483479942392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree114.table
  base := (63984115172654948733089727971541132948583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3026452)
      previous := (1513226)
      next := (1513226)
      square := (14788383496113770329549730220110000000000000)
      linear := (-1753331375015489840866926898118923500000000000)
      constant := (53277756831289780693917468966905212846415573767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53109013631783360969/10000000000000000000)
  centralHi := (531090136317833609691/100000000000000000000)
  directionLo := (533434916532789138693/100000000000000000000)
  directionHi := (266717458266394569347/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree115.table
  base := (65943404450861522261788774048969091927747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-14601235588385586831429788125011000000000000)
      constant := (447242167131771909779583910823962651535789243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree115.table
  base := (13188680889196683347954656590722828884863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-638502704121301600467820636289019397250000000000)
      constant := (19578188824590947910346259484794733844353834594035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533434916532789138693/100000000000000000000)
  centralHi := (266717458266394569347/50000000000000000000)
  directionLo := (535769434979816989049/100000000000000000000)
  directionHi := (10715388699596339781/2000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree116.table
  base := (4245579184513512067525918658478717225847/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-7364077163931361724503489535478000000000000)
      constant := (227596069369071118696907157157506225689345144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree116.table
  base := (13585853389612570869935495423916986810019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-644052781862011368382680662357107411000000000000)
      constant := (19926188561914854838471524609556337589091931748455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535769434979816989049/100000000000000000000)
  centralHi := (10715388699596339781/2000000000000000000)
  directionLo := (269046912610440938569/50000000000000000000)
  directionHi := (538093825220881877139/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree117.table
  base := (546419552200591052075283917762086101459/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361591850362212585690002695000000000000)
      linear := (-43949920317573550492852574014500000000000)
      constant := (1370451187381037833998051471051711010493376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree117.table
  base := (1748542566953491186411003592582486283143/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (3232394)
      previous := (1616197)
      next := (1616197)
      square := (15794693615671807955525007720295000000000000)
      linear := (-1921901951487340639933552332618921375000000000)
      constant := (59991921384798131267678049378807697287773137660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269046912610440938569/50000000000000000000)
  centralHi := (538093825220881877139/100000000000000000000)
  directionLo := (540408217945554194377/100000000000000000000)
  directionHi := (270204108972777097189/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree118.table
  base := (17995177909652250866369904775394050379591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-7490995903408498342080680481423000000000000)
      constant := (235651627460805469285940769684870939028301758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree118.table
  base := (17995177908899694556993529623374808750309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-327576468671715452106200357246641719250000000000)
      constant := (10315715711513574191992086612135800681964894631002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540408217945554194377/100000000000000000000)
  centralHi := (270204108972777097189/50000000000000000000)
  directionLo := (542712741056756683451/100000000000000000000)
  directionHi := (135678185264189170863/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree119.table
  base := (9255786727813003017605543145935065434957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-7554455273147066650869275954395500000000000)
      constant := (239732199749258062521563404650585041734030932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree119.table
  base := (37023146909970787276881709064155392802337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-330351507542070336063630370280685726125000000000)
      constant := (10494337273403656821548427693580133625617904891993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542712741056756683451/100000000000000000000)
  centralHi := (135678185264189170863/25000000000000000000)
  directionLo := (272503759876623931957/50000000000000000000)
  directionHi := (109001503950649572783/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree120.table
  base := (76138449232948091678999625627687703662469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-15235829285771269919315742854736000000000000)
      constant := (487695935065436613677925685916399221918957261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree120.table
  base := (76138449230766956546709729572048308566607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-666253092824850440042120766629459466000000000000)
      constant := (21348998799399303338390557480123706633638155302023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272503759876623931957/50000000000000000000)
  centralHi := (109001503950649572783/20000000000000000000)
  directionLo := (273646338304496361141/50000000000000000000)
  directionHi := (547292676608992722283/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree121.table
  base := (78257177869612073772797995612353731886247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-15362748025248406536892933800681000000000000)
      constant := (495997861622316781116370247652425655688775743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree121.table
  base := (78257177867755632845226153592544250643433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (9029332)
      previous := (4514666)
      next := (4514666)
      square := (44120714397496455280722748838510000000000000)
      linear := (-5552092318723638082289097460310309750000000000)
      constant := (179441356866121987046422428361950636117192703897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273646338304496361141/50000000000000000000)
  centralHi := (547292676608992722283/100000000000000000000)
  directionLo := (2198273326598252181/400000000000000000)
  directionHi := (549568331649563045251/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree122.table
  base := (80402479732236764420372703025749002575409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-15489666764725543154470124746626000000000000)
      constant := (504370179169112821544145013405071081435244121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree122.table
  base := (5025154983166049064927179299650767276223/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-338676624153134987935920409382817746750000000000)
      constant := (11039445345504916680973769316055191071720301158776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2198273326598252181/400000000000000000)
  centralHi := (549568331649563045251/100000000000000000000)
  directionLo := (275917301212851070743/50000000000000000000)
  directionHi := (551834602425702141487/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree123.table
  base := (8257435482062145296277706525361862971673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-7808292752101339886023657846285500000000000)
      constant := (256406443852895407429943996906263211711063685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree123.table
  base := (82574354819276850731574913561838557680533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-682903326046979743786700844833723507250000000000)
      constant := (22448458330025093231547794821893250666109015673437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275917301212851070743/50000000000000000000)
  centralHi := (551834602425702141487/100000000000000000000)
  directionLo := (110818320816836306527/20000000000000000000)
  directionHi := (138522901021045383159/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree124.table
  base := (84772803134614294593690375693831209151681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-15743504243679816389624506638516000000000000)
      constant := (521325987232325099291330989459031474346634089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree124.table
  base := (5298300195841879791108196752883134271217/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-344226701893844755850780435450905760500000000000)
      constant := (11410553548922732038919166295067067338250092258504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110818320816836306527/20000000000000000000)
  centralHi := (138522901021045383159/25000000000000000000)
  directionLo := (278169724718035232653/50000000000000000000)
  directionHi := (556339449436070465307/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree125.table
  base := (17399564934820840107103230365967933406587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-15870422983156953007201697584461000000000000)
      constant := (529909477748696900835060194799289778728566015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree125.table
  base := (86997824673130564640954087822965573337289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-694003481528399279616420896969899534750000000000)
      constant := (23196836994470164151056402347708579281116581916721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278169724718035232653/50000000000000000000)
  centralHi := (556339449436070465307/100000000000000000000)
  directionLo := (558578249022532773253/100000000000000000000)
  directionHi := (279289124511266386627/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree126.table
  base := (22312354859753502522348018962996943605973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-7998670861317044812389444265203000000000000)
      constant := (269281679627446589666483939061734716938818874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree126.table
  base := (44624709719092788265524965529778404183239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-349776779634554523765640461518993774250000000000)
      constant := (11787824009949328245851789041119290083193017606271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558578249022532773253/100000000000000000000)
  centralHi := (279289124511266386627/50000000000000000000)
  directionLo := (560808111178259674909/100000000000000000000)
  directionHi := (56080811117825967491/10000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree127.table
  base := (91527587429294743906075640466729928258423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-16124260462111226242356079476351000000000000)
      constant := (547287631750905657275032055698961232875673487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree127.table
  base := (45763793714294950409715053525003970951547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-352551818504909407723070474553037781125000000000)
      constant := (11978770087065303672199817350195210444351328391683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560808111178259674909/100000000000000000000)
  centralHi := (56080811117825967491/10000000000000000000)
  directionLo := (112605828418528300123/20000000000000000000)
  directionHi := (70378642761580187577/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree128.table
  base := (93832328644920769164439364660751769409507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-16251179201588362859933270422296000000000000)
      constant := (556082295236730002714482183234515049030206683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree128.table
  base := (46916164322160557242220969625655405590103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-355326857375264291680500487587081788000000000000)
      constant := (12171256728582925590201541608417701431397237865167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112605828418528300123/20000000000000000000)
  centralHi := (70378642761580187577/12500000000000000000)
  directionLo := (565241445868776082533/100000000000000000000)
  directionHi := (282620722934388041267/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree129.table
  base := (48081821542942866895247887008047130558819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-8189048970532749738755230684120500000000000)
      constant := (282473674856182571075407188776747902564440411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree129.table
  base := (96163643085375599645616108702136590335437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-716203792491238351275861001242251589750000000000)
      constant := (24730567869004361292198307757231609137879923287893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell105.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565241445868776082533/100000000000000000000)
  centralHi := (282620722934388041267/50000000000000000000)
  directionLo := (567445124580406586631/100000000000000000000)
  directionHi := (70930640572550823329/12500000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree130.table
  base := (98521530752199149166888775199198626338337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (723183700724425171380005390000000000000)
      linear := (-97662820594926840799335220794000000000000)
      constant := (3395756184484098716021866620606698626338337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree130.table
  base := (49260765375882598282687981377185871312353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (3232394)
      previous := (1616197)
      next := (1616197)
      square := (15794693615671807955525007720295000000000000)
      linear := (-2135366479976177867428168719853075750000000000)
      constant := (74324566300728476584781955110676271904169891393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567445124580406586631/100000000000000000000)
  centralHi := (70930640572550823329/12500000000000000000)
  directionLo := (569640278326876899981/100000000000000000000)
  directionHi := (284820139163438449991/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree131.table
  base := (4036239665755340784621989972345828669053/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-16631935420019772712664843260131000000000000)
      constant := (582888631633076428515531830627284001126748925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree131.table
  base := (20181198328702878612811393067789519826323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-727303947972657887105581053378427617250000000000)
      constant := (25515920079091623332046194831960740098930592143735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569640278326876899981/100000000000000000000)
  centralHi := (284820139163438449991/50000000000000000000)
  directionLo := (571827005286188289113/100000000000000000000)
  directionHi := (285913502643094144557/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree132.table
  base := (103317025760971932828841708772352365106501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-16758854159496909330242034206076000000000000)
      constant := (591964859078161970494332841888069549702998669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree132.table
  base := (5165851288032898302287716658721721392171/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 305045000000000000000000000000000000000000000
      center := (4514666)
      previous := (2257333)
      next := (2257333)
      square := (22060357198748227640361374419255000000000000)
      linear := (-3028322420303172128183640824159155500000000000)
      constant := (107079412716284350237889112087515964441649605390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571827005286188289113/100000000000000000000)
  centralHi := (285913502643094144557/50000000000000000000)
  directionLo := (574005401766236899079/100000000000000000000)
  directionHi := (14350135044155922477/2500000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree133.table
  base := (105754633103506038836094556410998853356641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-16885772898974045947819225152021000000000000)
      constant := (601111477513076347799055246241583681217272329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree133.table
  base := (21150926620647800804237560510870050368259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (3026452)
      previous := (1513226)
      next := (1513226)
      square := (14788383496113770329549730220110000000000000)
      linear := (-2045440729789688152175349322755134750000000000)
      constant := (72890849873667898740848261092626675792090141455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574005401766236899079/100000000000000000000)
  centralHi := (14350135044155922477/2500000000000000000)
  directionLo := (576175562254307751807/100000000000000000000)
  directionHi := (4501371580111779311/781250000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree134.table
  base := (108218813671534356410333023597157035696931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-17012691638451182565396416097966000000000000)
      constant := (610328486937827760102340223289791039032781339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree134.table
  base := (54109406835653625320642232157043882165057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-371977090597393595425080565791345829250000000000)
      constant := (13358528430125943303867847468398396504157338464073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576175562254307751807/100000000000000000000)
  centralHi := (4501371580111779311/781250000000000000)
  directionLo := (1156675158929794423/200000000000000000)
  directionHi := (578337579464897211501/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree135.table
  base := (27677391866277713842767410025150191234691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-8569805188964159591486803521955500000000000)
      constant := (309807943676212664151842695281891702137325558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree135.table
  base := (22141913492983543728732265869879449944859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-749504258935496958765021157650779672250000000000)
      constant := (27123598044914544353362805594600950858312158652255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1156675158929794423/200000000000000000)
  centralHi := (578337579464897211501/100000000000000000000)
  directionLo := (290245772192966200087/50000000000000000000)
  directionHi := (23219661775437296007/4000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree136.table
  base := (28306723621073442824770305802251983389711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-8633264558702727900275398994928000000000000)
      constant := (314486839378439447108121015092589170385722318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree136.table
  base := (56613447242064765767699873527831408750709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-377527168338103363339940591859433843000000000000)
      constant := (13766610179191260568659410439663762598143112651101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290245772192966200087/50000000000000000000)
  centralHi := (23219661775437296007/4000000000000000000)
  directionLo := (291318773161726377499/50000000000000000000)
  directionHi := (582637546323452754999/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree137.table
  base := (904459333821442312350321428058282189841/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-8696723928441296209063994467900500000000000)
      constant := (319200930575599426665962070830925317665320256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree137.table
  base := (115770794729004957018719372788988172144747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-760604414416916494594741209786955699750000000000)
      constant := (27945923800656276625323351784364600261962030736483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291318773161726377499/50000000000000000000)
  centralHi := (582637546323452754999/100000000000000000000)
  directionLo := (584775672944815808899/100000000000000000000)
  directionHi := (5847756729448158089/1000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree138.table
  base := (59170634099863676320066757054543529070269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-8760183298179864517852589940873000000000000)
      constant := (323950217267698007717775620236465606412875461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree138.table
  base := (2958531704990215045120414111479572030389/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-383077246078813131254800617927521856750000000000)
      constant := (14180854185868143874934223560139122128064221052420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584775672944815808899/100000000000000000000)
  centralHi := (5847756729448158089/1000000000000000000)
  directionLo := (73363251290060791953/12500000000000000000)
  directionHi := (939049616512778137/160000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree139.table
  base := (60469157448053854929030087052670972796659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-8823642667918432826641185413845500000000000)
      constant := (328734699454740744328664768530931831902635371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree139.table
  base := (48375325958402696887373693862736823457/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-385852284949168015212230630961565863625000000000)
      constant := (14390287035811521884340975984965725436385920841250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73363251290060791953/12500000000000000000)
  centralHi := (939049616512778137/160000000000000000)
  directionLo := (589028642964465219719/100000000000000000000)
  directionHi := (14725716074111630493/2500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree140.table
  base := (6178096740917630608501282030722630420149/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-8887102037657001135429780886818000000000000)
      constant := (333554377136733291621871197471316245410051810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree140.table
  base := (4942477392730670760375023416254665704137/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-777254647639045798339321287991219741000000000000)
      constant := (29202520900317042166276690303153328009204675054825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589028642964465219719/100000000000000000000)
  centralHi := (14725716074111630493/2500000000000000000)
  directionLo := (9236619591772059077/1562500000000000000)
  directionHi := (591143653873411780929/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree141.table
  base := (31553031991632427194344325138158519052063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-8950561407395569444218376359790500000000000)
      constant := (338409250313681365954908761252039016939597294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree141.table
  base := (25242425593291345634668827181419557406777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-782804725379755566254181314059307754750000000000)
      constant := (29627548857818785264249039116286620805141872585765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9236619591772059077/1562500000000000000)
  centralHi := (591143653873411780929/100000000000000000000)
  directionLo := (148312781141127698063/25000000000000000000)
  directionHi := (593251124564510792253/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree142.table
  base := (12888889434070698472179440210452088217469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9014020777134137753006971832763000000000000)
      constant := (343299318985590712063799356344701764543761305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree142.table
  base := (16111111792580617805151912009297663168949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-394177401560232667084520670063697884250000000000)
      constant := (15027828972064388713539521866618947260505189217844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148312781141127698063/25000000000000000000)
  centralHi := (593251124564510792253/100000000000000000000)
  directionLo := (297675567556066536437/50000000000000000000)
  directionHi := (4762809080897064583/800000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree143.table
  base := (32898058485238110331580408287081619182277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361591850362212585690002695000000000000)
      linear := (-53712900277353290306482646779500000000000)
      constant := (2060500492026432402723906857248600738364554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree143.table
  base := (131592233940899700505833321400215395777607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (53428)
      previous := (26714)
      next := (26714)
      square := (261069315961517486868181945790000000000000)
      linear := (-38823653032479588345831158794830250000000000)
      constant := (1490872324282239853683552942011238625063216127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297675567556066536437/50000000000000000000)
  centralHi := (4762809080897064583/800000000000000000)
  directionLo := (149360941045834075873/25000000000000000000)
  directionHi := (597443764183336303493/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree144.table
  base := (13432214676733383477907476424579505161253/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9140939516611274370584162778708000000000000)
      constant := (353185042814316183342427251455441681861258785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree144.table
  base := (134322146767289003088473040530907405770483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-799454958601884869998761392263571796000000000000)
      constant := (30921119503175523274313345228663183534156819078987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149360941045834075873/25000000000000000000)
  centralHi := (597443764183336303493/100000000000000000000)
  directionLo := (299764544536125297409/50000000000000000000)
  directionHi := (599529089072250594819/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree145.table
  base := (34269658204979615870995119641242185659221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9204398886349842679372758251680500000000000)
      constant := (358180697971143720625192138813685796252816698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree145.table
  base := (6853931640994017833104861819548449699551/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-402502518171297318956810709165829904875000000000)
      constant := (15679235987956638642442822221450207268749681170390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299764544536125297409/50000000000000000000)
  centralHi := (599529089072250594819/100000000000000000000)
  directionLo := (300803592866695666679/50000000000000000000)
  directionHi := (601607185733391333359/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree146.table
  base := (139861692098772996277981325939604825892109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-18535716512176821976322707449306000000000000)
      constant := (726423097245910642850713132821396715575766421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree146.table
  base := (69930846049370303547584117376265960788973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-405277557041652202914240722199873911750000000000)
      constant := (15899452788730639130921071467948191017199083904597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300803592866695666679/50000000000000000000)
  centralHi := (601607185733391333359/100000000000000000000)
  directionLo := (7545976610174249069/1250000000000000000)
  directionHi := (603678128813939925521/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree147.table
  base := (71335662301981667429293430705832732480173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9331317625826979296949949197625500000000000)
      constant := (368277594769756554436360091647525169289149237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree147.table
  base := (142671324603935806699964964832432664308147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-816105191824014173743341470467835837250000000000)
      constant := (32242420307820013809230739555954473187484552079083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7545976610174249069/1250000000000000000)
  centralHi := (603678128813939925521/100000000000000000000)
  directionLo := (969187186696050009/160000000000000000)
  directionHi := (302870995842515627813/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree148.table
  base := (36376882583888626203869202599419419111463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9394776995565547605738544670598000000000000)
      constant := (373378836411552914320530651321862763659674494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree148.table
  base := (36376882583882777299623608793414675382579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-410827634782361970829100748267961925500000000000)
      constant := (16344508083494982448812985649381390947598114455062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (969187186696050009/160000000000000000)
  centralHi := (302870995842515627813/50000000000000000000)
  directionLo := (607798846472084959903/100000000000000000000)
  directionHi := (18993713952252654997/3125000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree149.table
  base := (14837030929361057054543946924537323497721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9458236365304115914527140143570500000000000)
      constant := (378515273548349814519396856475094475855574245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree149.table
  base := (74185154646795343993511668533803985764653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-413602673652716854786530761302005932375000000000)
      constant := (16569346577485802630375255573584966336184245250117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607798846472084959903/100000000000000000000)
  centralHi := (18993713952252654997/3125000000000000000)
  directionLo := (152462191021053997943/25000000000000000000)
  directionHi := (609848764084215991773/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree150.table
  base := (151259661478194570076897164826859890904309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-19043391470085368446631471233086000000000000)
      constant := (767373812360305163492720787455826821562828221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree150.table
  base := (151259661478177673812182782497740410209887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-832755425046143477487921548672099878500000000000)
      constant := (33591451271765400935394626420006793293784644513943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152462191021053997943/25000000000000000000)
  centralHi := (609848764084215991773/100000000000000000000)
  directionLo := (122378362848551681721/20000000000000000000)
  directionHi := (305945907121379204303/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree151.table
  base := (77087793444684233230134644741595430121631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9585155104781252532104331089515500000000000)
      constant := (388893734306966451879181701733138565190555639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree151.table
  base := (154175586889354108588774030292106612944079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-838305502786853245402781574740187892250000000000)
      constant := (34047290517371809920495110427254068950983930701031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122378362848551681721/20000000000000000000)
  centralHi := (305945907121379204303/50000000000000000000)
  directionLo := (306964032754467421151/50000000000000000000)
  directionHi := (613928065508934842303/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree152.table
  base := (78559042763596556455857601011400549117741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9648614474519820840892926562488000000000000)
      constant := (394135757928796567014626246310082692800898229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree152.table
  base := (78559042763590456304881272016027017421853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102245000000000000000000000000000000000000000
      center := (1513226)
      previous := (756613)
      next := (756613)
      square := (7394191748056885164774865110055000000000000)
      linear := (-1168775042281943231741885873695673000000000000)
      constant := (47792535861206761682931496253456406229259471997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306964032754467421151/50000000000000000000)
  centralHi := (613928065508934842303/100000000000000000000)
  directionLo := (38497349081918920051/6250000000000000000)
  directionHi := (615957585310702720817/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree153.table
  base := (40021789347932057336449501013420077029349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9712073844258389149681522035460500000000000)
      constant := (399412977045647973485474609544620923535919962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree153.table
  base := (160087157391717862837627547795887154241367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-849405658268272781232501626876363919750000000000)
      constant := (34968212395024258257996087316028148961558686175663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38497349081918920051/6250000000000000000)
  centralHi := (615957585310702720817/100000000000000000000)
  directionLo := (617980439968806981423/100000000000000000000)
  directionHi := (38623777498050436339/6250000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree154.table
  base := (163082802483032388310324957083794901291747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-19551066427993914916940235016866000000000000)
      constant := (809450783315051241344033010068352838318305243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree154.table
  base := (40770700620755895084001523563024599697927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 305045000000000000000000000000000000000000000
      center := (4514666)
      previous := (2257333)
      next := (2257333)
      square := (22060357198748227640361374419255000000000000)
      linear := (-3532874942185878302261825012167156750000000000)
      constant := (146418574492029634856044606929125779090316656686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617980439968806981423/100000000000000000000)
  centralHi := (38623777498050436339/6250000000000000000)
  directionLo := (123999338944413550997/20000000000000000000)
  directionHi := (309998347361033877493/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree155.table
  base := (332210041602326017310061255960777022961/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-9838992583735525767258712981405500000000000)
      constant := (410073001764434360467054503679031266720102250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree155.table
  base := (83052510400577762606105740298414313141221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-430252906874846158531110839506269973625000000000)
      constant := (17950729393966223121101399644120878150572206740669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123999338944413550997/20000000000000000000)
  centralHi := (309998347361033877493/50000000000000000000)
  directionLo := (15550160343798257509/2500000000000000000)
  directionHi := (622006413751930300361/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree156.table
  base := (42288453086544088883535295567353436294631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (361591850362212585690002695000000000000)
      linear := (-58594390257243160213297683162000000000000)
      constant := (2458318386783307380332075245361706872589262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree156.table
  base := (21144226543271249712976154165865589730699/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (3232394)
      previous := (1616197)
      next := (1616197)
      square := (15794693615671807955525007720295000000000000)
      linear := (-2562295536953852322417401494321384500000000000)
      constant := (107611549342036975421540030799229834737606652076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15550160343798257509/2500000000000000000)
  centralHi := (622006413751930300361/100000000000000000000)
  directionLo := (124801932041260665181/20000000000000000000)
  directionHi := (312004830103151662953/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree157.table
  base := (172229177118127545569013255323148729614027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-19931822646425324769671807854701000000000000)
      constant := (841747616926728076907439558168851010304770563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree157.table
  base := (86114588559061072131836516189809947327841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-435802984615555926445970865574357987375000000000)
      constant := (18423514848049866541009568026798196056411778189849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124801932041260665181/20000000000000000000)
  centralHi := (312004830103151662953/50000000000000000000)
  directionLo := (78250812027838843463/12500000000000000000)
  directionHi := (125201299244542149541/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree158.table
  base := (175331115117070556187578801486923534392723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-20058741385902461387248998800646000000000000)
      constant := (852654010110788390185023883352205577312370187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree158.table
  base := (175331115117065967684292338089849504185237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-877156046971821620806801757216803988500000000000)
      constant := (37324436843406551064239021946366342759970042020093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78250812027838843463/12500000000000000000)
  centralHi := (125201299244542149541/20000000000000000000)
  directionLo := (125599396590156179733/20000000000000000000)
  directionHi := (313998491475390449333/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree159.table
  base := (223074532928822797897273252922374052349/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-10092830062689799002413094873295500000000000)
      constant := (431815397142473883095911580284430423438792400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree159.table
  base := (178459626343054340459026166103851348041941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-882706124712531388721661783284892002250000000000)
      constant := (37804925119529341948591816250902456049382771694749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125599396590156179733/20000000000000000000)
  centralHi := (313998491475390449333/50000000000000000000)
  directionLo := (629981180574096216227/100000000000000000000)
  directionHi := (157495295143524054057/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree160.table
  base := (181614710796142331747632678504009374050463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-20312578864856734622403380692536000000000000)
      constant := (874677969449214948951992493304937584214528247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree160.table
  base := (45403677699034755177525718892080605275977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-444128101226620578318260904676490008000000000000)
      constant := (19144247262234243909071140796374806626642263551906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629981180574096216227/100000000000000000000)
  centralHi := (157495295143524054057/25000000000000000000)
  directionLo := (315979574165712748241/50000000000000000000)
  directionHi := (631959148331425496483/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree161.table
  base := (184796368476373482577242943051348341814059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-20439497604333871239980571638481000000000000)
      constant := (885795535603598497656469384868605744766575971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree161.table
  base := (46199092119092667531085798075411088290141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-446903140096975462275690917710534014875000000000)
      constant := (19387572529112181330985709348471852699372951119098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315979574165712748241/50000000000000000000)
  centralHi := (631959148331425496483/100000000000000000000)
  directionLo := (633930944537359906559/100000000000000000000)
  directionHi := (495258550419812427/78125000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree162.table
  base := (94002299691900631142999998995653795178933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-10283208171905503928778881292213000000000000)
      constant := (448491746374053394942632043499895241385239677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree162.table
  base := (188004599383798873431114364724508827719083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-899356357934660692466241861489156043500000000000)
      constant := (39264876720797332518964457505011387934976687704387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633930944537359906559/100000000000000000000)
  centralHi := (495258550419812427/78125000000000000)
  directionLo := (635896626602373092849/100000000000000000000)
  directionHi := (12717932532047461857/2000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree163.table
  base := (95619701759237094007998619671532506210821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-10346667541644072237567476765185500000000000)
      constant := (454120920441374012517695191812866431049628749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree163.table
  base := (95619701759236079517837913666301922714641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36910445000000000000000000000000000000000000000
      center := (546274586)
      previous := (273137293)
      next := (273137293)
      square := (2669303221048535544483726304729855000000000000)
      linear := (-452453217837685230190550943778622028625000000000)
      constant := (19878844756093877815064025615244749899502945215049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635896626602373092849/100000000000000000000)
  centralHi := (12717932532047461857/2000000000000000000)
  directionLo := (159464062763081226963/25000000000000000000)
  directionHi := (637856251052324907853/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree164.table
  base := (97250390440219871871302732997311325606121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-10410126911382640546356072238158000000000000)
      constant := (459785290003765113949342969879252614027434449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree164.table
  base := (194500780880438020487186707358384752587337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-910456513416080228295961913625332071000000000000)
      constant := (40253583432395982597069018425770350045717702006993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159464062763081226963/25000000000000000000)
  centralHi := (637856251052324907853/100000000000000000000)
  directionLo := (639809873547427501089/100000000000000000000)
  directionHi := (63980987354742750109/10000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree165.table
  base := (49447182867436100514735420616243062801799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-10473586281121208855144667711130500000000000)
      constant := (465484855061230626171693764580908592727008062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree165.table
  base := (49447182867435734629045852065328934882647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 305045000000000000000000000000000000000000000
      center := (4514666)
      previous := (2257333)
      next := (2257333)
      square := (22060357198748227640361374419255000000000000)
      linear := (-3785151203127231389300917106171157375000000000)
      constant := (168399001989348580763127949747651286035104571646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639809873547427501089/100000000000000000000)
  centralHi := (63980987354742750109/10000000000000000000)
  directionLo := (641757548900691777657/100000000000000000000)
  directionHi := (320878774450345888829/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree166.table
  base := (40220651057286729269814837326331610770917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (122218045422427853963220910910000000000000)
      linear := (-21074091301719554327866526368206000000000000)
      constant := (942439231227548785061402694176973711101424865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree166.table
  base := (201103255286432403422963621243800723021493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-921556668897499764125681965761508098500000000000)
      constant := (41254614659267213286397321752923946050827760238877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641757548900691777657/100000000000000000000)
  centralHi := (320878774450345888829/50000000000000000000)
  directionLo := (321849665547935759913/50000000000000000000)
  directionHi := (643699331095871519827/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree167.table
  base := (25555544041318999145609315502180469710071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-10600505020598345472721858657075500000000000)
      constant := (476989571661400174674998862998660935024007996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree167.table
  base := (204444352330550937637433669496347833320553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-927106746638209532040541991829596112250000000000)
      constant := (41759751965930881490770156907202449509521675275217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321849665547935759913/50000000000000000000)
  centralHi := (643699331095871519827/100000000000000000000)
  directionLo := (645635273304921790839/100000000000000000000)
  directionHi := (16140881832623044771/2500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree168.table
  base := (103906011301071507327531903010448923129863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (61109022711213926981610455455000000000000)
      linear := (-10663964390336913781510454130048000000000000)
      constant := (482794723204111654451153246224609868008946847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree168.table
  base := (207812022602142118303771875126855406611763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (1092549172)
      previous := (546274586)
      next := (546274586)
      square := (5338606442097071088967452609459710000000000000)
      linear := (-932656824378919299955402017897684126000000000000)
      constant := (42267970401413682848152159507438294717239222912907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell105.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645635273304921790839/100000000000000000000)
  centralHi := (16140881832623044771/2500000000000000000)
  directionLo := (161891356976246898543/25000000000000000000)
  directionHi := (647565427904987594173/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree169.table
  base := (211206266101249360923185624576549593648029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (148)
      previous := (74)
      next := (74)
      square := (723183700724425171380005390000000000000)
      linear := (-126951760474266060240225439089000000000000)
      constant := (5782663553158727050803715151299424593648029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree169.table
  base := (105603133050624299885364642443897350568317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (3232394)
      previous := (1616197)
      next := (1616197)
      square := (15794693615671807955525007720295000000000000)
      linear := (-2775760065442689549912017881555538875000000000)
      constant := (126565887472532343895686529052075104947518404877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell105.Kernel169
