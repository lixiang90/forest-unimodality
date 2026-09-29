import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell077.Parameters
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch000_049
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_99.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_99.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree000.table
  base := (219486001849594270735011037/5000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (260281876347890281375718750000000000000)
      linear := (3257801145027130985606933500000000000)
      constant := (109743000924797135367505518500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree000.table
  base := (219486001849594270735011037/5000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (260281876347890281375718750000000000000)
      linear := (3257801145027130985606933500000000000)
      constant := (109743000924797135367505518500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree001.table
  base := (128938895061385380015669165729684839555063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-1326820136779962013676376124776387000000000000)
      constant := (337458405261006087980965035457950210451388120407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree001.table
  base := (12870271425065318556882774749001776060227/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-2493325055304820599117289757266500000000000)
      constant := (631316784377082693833212298059173535831424135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12498995418557205427/25000000000000000000)
  directionHi := (49995981674228821709/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree002.table
  base := (155530129574472978223351794815682461691003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-5341353094392207431064006928490274000000000000)
      constant := (409282916924115793352190399381396483076386943067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree002.table
  base := (30999381195290485208023275642182010381753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-20074319278528208436098052279066000000000000)
      constant := (1528997235290154567769220800469861418757805765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/25000000000000000000)
  centralHi := (49995981674228821709/100000000000000000000)
  directionLo := (70704995347851118773/100000000000000000000)
  directionHi := (35352497673925559387/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree003.table
  base := (24243873103989653092973892799087174555427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (75617350998465432435555186968750000000000000)
      linear := (-223029608756235856521535044650771500000000000)
      constant := (7207804975833494356890771474537100789017207467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree003.table
  base := (19303703420025970626286718087805350853947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-3352815370648570497302993947674000000000000)
      constant := (107587340804680512839248677217222135399741415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70704995347851118773/100000000000000000000)
  centralHi := (35352497673925559387/50000000000000000000)
  directionLo := (21648895108511705121/25000000000000000000)
  directionHi := (17319116086809364097/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree004.table
  base := (31426307954266150841984172513562225987827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-5358389368028387119243258143182637000000000000)
      constant := (87443658215352776116535187602106776105885390803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree004.table
  base := (15624506320182210185384577176390300454807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-10069089348286515128838959694766500000000000)
      constant := (163071560632468288626639135468167334757563407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/25000000000000000000)
  centralHi := (17319116086809364097/20000000000000000000)
  directionLo := (12498995418557205427/12500000000000000000)
  directionHi := (99991963348457643417/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree005.table
  base := (5304328571453896981218818078885102031687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-3351122889222264410549442741325693500000000000)
      constant := (31863623990393402174921594923913172092259300686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree005.table
  base := (21084821674693145722250449899827223812957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-25188688225227493277492366014533000000000000)
      constant := (237741140555686483378819903061621620590791557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/12500000000000000000)
  centralHi := (99991963348457643417/100000000000000000000)
  directionLo := (55897206812704695447/50000000000000000000)
  directionHi := (22358882725081878179/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree006.table
  base := (2975777283660901920073598492828396238321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (151234701996930864871110373937500000000000000)
      linear := (-894011354317852280328279202457793000000000000)
      constant := (5643841467177997847102500999843663017766276205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree006.table
  base := (29560453734568447960497461447792884474461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-6719821723084879177179291697674000000000000)
      constant := (42148179763113521911881535724890451192688029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55897206812704695447/50000000000000000000)
  centralHi := (22358882725081878179/20000000000000000000)
  directionLo := (122464644291399242379/100000000000000000000)
  directionHi := (6123232214569962119/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree007.table
  base := (4301885134869979771347135500344190294357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4695768)
      previous := (2347884)
      next := (2347884)
      square := (55555604815199093217958912875000000000000000)
      linear := (-383263616297012743869801639248526000000000000)
      constant := (1808771199555520417366894370892288691485919385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree007.table
  base := (21359564186956281474432167235502934315253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-70579414565072838634242518529066000000000000)
      constant := (331390197864243544437684393386726259223794653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122464644291399242379/100000000000000000000)
  centralHi := (6123232214569962119/5000000000000000000)
  directionLo := (132276934062552149927/100000000000000000000)
  directionHi := (16534616757819018741/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree008.table
  base := (7921120259942199376744887505299838172933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-10733815009692953926665767501057637000000000000)
      constant := (41873093163004954394720641120806474572548012837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree008.table
  base := (3931078486934678457494445413459034291193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-20170108405595441168467852944766500000000000)
      constant := (78398025750732782859932071622043995087982593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132276934062552149927/100000000000000000000)
  centralHi := (16534616757819018741/12500000000000000000)
  directionLo := (70704995347851118773/50000000000000000000)
  directionHi := (141409990695702237547/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree009.table
  base := (11721152080993663889588698221021659070213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-2683926982246465695226976631228086000000000000)
      constant := (9359107246525084499828308987039507414737350973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree009.table
  base := (1162426704981677847157792392678915837159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (62988214076189448092923937500000000000000)
      linear := (-560379337528954880947532747093000000000000)
      constant := (1949629817102144981494181560757744081481195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70704995347851118773/50000000000000000000)
  centralHi := (141409990695702237547/100000000000000000000)
  directionLo := (37496986255671616281/25000000000000000000)
  directionHi := (1199903560181491721/800000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree010.table
  base := (214051707789180114121939603047104934739/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-6710763915262618665188511089997568500000000000)
      constant := (22139976602103866343602525371828221297077811710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree010.table
  base := (1059874828951850022060677386961653848913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-25220617934249904188282299569766500000000000)
      constant := (83111308974697354566631677670137338746392626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37496986255671616281/25000000000000000000)
  centralHi := (1199903560181491721/800000000000000000)
  directionLo := (39525293986650372653/25000000000000000000)
  directionHi := (158101175946601490613/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree011.table
  base := (94245405451279028707761378969841533477/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 54022500000000000000000000000000000000000000
      center := (475398)
      previous := (237699)
      next := (237699)
      square := (5624431066001561090247906468750000000000000)
      linear := (-61013984466699913356333262477123500000000000)
      constant := (198054912839158386833669622853263641150471888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree011.table
  base := (5957848846278593096629355472339571789353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (84331327936716451165732875000000000000000)
      linear := (-917218932184368122254199103546000000000000)
      constant := (2976586135773876444100770037565505314937593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525293986650372653/25000000000000000000)
  centralHi := (158101175946601490613/100000000000000000000)
  directionLo := (20727239029862697319/12500000000000000000)
  directionHi := (165817912238901578553/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree012.table
  base := (1968326885761237890603000394773679430853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (151234701996930864871110373937500000000000000)
      linear := (-1789915627928613414898697428770293000000000000)
      constant := (5867903846823699463509372410246135121930844413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree012.table
  base := (3869172261005462069691760534256111191177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-13453834427957496536931887197674000000000000)
      constant := (44125197008133018458353150638292905087191753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20727239029862697319/12500000000000000000)
  centralHi := (165817912238901578553/100000000000000000000)
  directionLo := (21648895108511705121/12500000000000000000)
  directionHi := (173191160868093640969/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree013.table
  base := (432368975855072376609195241298447522223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-34906194123547324871887808396802774000000000000)
      constant := (117550116536184408798085738499431694267168668235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree013.table
  base := (2099040605408417334848344323900158020929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-131185528908926394872015878029066000000000000)
      constant := (442208176854400880787643388404303448763125129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/12500000000000000000)
  centralHi := (173191160868093640969/100000000000000000000)
  directionLo := (90131537746794981473/50000000000000000000)
  directionHi := (180263075493589962947/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree014.table
  base := (159098735220662483978068587401952929637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 133402500000000000000000000000000000000000000
      center := (1173942)
      previous := (586971)
      next := (586971)
      square := (13888901203799773304489728218750000000000000)
      linear := (-191805647675406164671423791202756500000000000)
      constant := (670697853127621508457054061031177860278359957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree014.table
  base := (115455741550078416221271479493167506147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-141286547966235320911644771279066000000000000)
      constant := (494723346914055201909048335225686673638733735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90131537746794981473/50000000000000000000)
  centralHi := (180263075493589962947/100000000000000000000)
  directionLo := (23383479267549109491/12500000000000000000)
  directionHi := (187067834140392875929/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree015.table
  base := (-85674665777682213982579113163314518507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (75617350998465432435555186968750000000000000)
      linear := (-1118933882366996991091953270963271500000000000)
      constant := (4089521184236225778489544102970277655537655706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree015.table
  base := (-92673387960366711076115813331247316981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (283446963342852516418157718750000000000000)
      linear := (-4205210195098451304202046236918500000000000)
      constant := (15395237666546891088835105669967043343615382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23383479267549109491/12500000000000000000)
  centralHi := (187067834140392875929/100000000000000000000)
  directionLo := (96816802200789717329/50000000000000000000)
  directionHi := (193633604401579434659/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree016.table
  base := (-917322464096704746753061255854415120561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-21484666293022087541510786216807637000000000000)
      constant := (82383357979850573952383084290414367182835479471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree016.table
  base := (-943910420126426404389037373595137728643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-80744293040426586495451278889533000000000000)
      constant := (310210652961973740791972877200322055121569957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96816802200789717329/50000000000000000000)
  centralHi := (193633604401579434659/100000000000000000000)
  directionLo := (12498995418557205427/6250000000000000000)
  directionHi := (199983926696915286833/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree017.table
  base := (-708451294683775860874021446777823045513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-11414261351719114621683206778138193500000000000)
      constant := (46007480075874743306288765886678130138950659543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree017.table
  base := (-1442170510043478124971767571126414599741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-85794802569081049515265725514533000000000000)
      constant := (346541426451332444982203827503001010507938459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/6250000000000000000)
  centralHi := (199983926696915286833/100000000000000000000)
  directionLo := (206138713299290317851/100000000000000000000)
  directionHi := (51534678324822579463/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree018.table
  base := (-1850011707464166641669082252482588453499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (151234701996930864871110373937500000000000000)
      linear := (-2685819901539374549469115655082793000000000000)
      constant := (11387085885534919213494176569088767419901017021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree018.table
  base := (-3748020363032279715288561422167933499039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (125976428152378896185847875000000000000000)
      linear := (-2243094125870012655187164744186000000000000)
      constant := (9531430459316290214969758470665680046616281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206138713299290317851/100000000000000000000)
  centralHi := (51534678324822579463/25000000000000000000)
  directionLo := (1325718662772208477/625000000000000000)
  directionHi := (212114986043553356321/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree019.table
  base := (-444703682231142096875615039022056357137/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-25516235524270512647077668235213887000000000000)
      constant := (113771837200085928130948513704983307928069073035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree019.table
  base := (-898512400520504861198782611087542895737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-191791643252779951109789237529066000000000000)
      constant := (857176044418243549435701474203608960394408315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1325718662772208477/625000000000000000)
  centralHi := (212114986043553356321/100000000000000000000)
  directionLo := (54481857925268721573/25000000000000000000)
  directionHi := (217927431701074886293/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree020.table
  base := (-317892212273927734508396152362095285753/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-13430045967343327174466647787341318500000000000)
      constant := (62932104950407246623400292787464204257559096732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree020.table
  base := (-1282345875807913861976952151106966024079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-50473165577522219287354532694766500000000000)
      constant := (237090370248629930223780594778830625998001721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54481857925268721573/25000000000000000000)
  centralHi := (217927431701074886293/100000000000000000000)
  directionLo := (55897206812704695447/25000000000000000000)
  directionHi := (223588827250818781789/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree021.table
  base := (-2813756731405158970108938123909574249681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (260876)
      previous := (130438)
      next := (130438)
      square := (3086422489733282956553272937500000000000000)
      linear := (-63954531394790920750088260576307000000000000)
      constant := (314621570660084060153787354002062134273641351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree021.table
  base := (-5668258202185110175129129327886149628187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-23554853485266422576560780447674000000000000)
      constant := (116167376494989941491067779515785983054904357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55897206812704695447/25000000000000000000)
  centralHi := (223588827250818781789/100000000000000000000)
  directionLo := (114555185232889292003/50000000000000000000)
  directionHi := (229110370465778584007/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree022.table
  base := (-243170721214599958909403030013108252713/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (1901592)
      previous := (950796)
      next := (950796)
      square := (22497724264006244360991625875000000000000000)
      linear := (-488393467033370871944538020720994000000000000)
      constant := (2519213401923309721507992334362261594178119575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree022.table
  base := (-764713448746510279725157544559690589101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (1782)
      previous := (891)
      next := (891)
      square := (21082831984179112791433218750000000000000)
      linear := (-458873347984931258736933713386500000000000)
      constant := (2372990181138289667487622037434330124565638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114555185232889292003/50000000000000000000)
  centralHi := (229110370465778584007/100000000000000000000)
  directionLo := (234501940372646238431/100000000000000000000)
  directionHi := (7328185636645194951/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree023.table
  base := (-6449053145053831083973489464372369484307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-61783322331870158909000355186177774000000000000)
      constant := (333694561839768141221075963425410750605446814477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree023.table
  base := (-324262613059915557049138410955622894683/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-58048929870503913817076202632266500000000000)
      constant := (314337587323714261234810129998474200046059585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234501940372646238431/100000000000000000000)
  centralHi := (7328185636645194951/3125000000000000000)
  directionLo := (239772304952231620333/100000000000000000000)
  directionHi := (119886152476115810167/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree024.table
  base := (-3371775555510303415214627680346988497623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (151234701996930864871110373937500000000000000)
      linear := (-3581724175150135684039533881395293000000000000)
      constant := (20227109655344317055317488257665094554682068417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree024.table
  base := (-3388790637887459141900772920961691644703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (566893926685705032836315437500000000000000)
      linear := (-13460929918851365628218539098837000000000000)
      constant := (76217229658360839456247327705560717798918433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239772304952231620333/100000000000000000000)
  centralHi := (119886152476115810167/50000000000000000000)
  directionLo := (244929288582798484759/100000000000000000000)
  directionHi := (6123232214569962119/2500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree025.table
  base := (-6968734641282484970782837067662032253373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-67158747973534725716422864544052774000000000000)
      constant := (395989440714983051808808085331518678549460404003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree025.table
  base := (-280026934439430102694231167326075139033/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-252397757596633507347562597029066000000000000)
      constant := (1492148003831737391803979881660078439058439175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244929288582798484759/100000000000000000000)
  centralHi := (6123232214569962119/2500000000000000000)
  directionLo := (12498995418557205427/5000000000000000000)
  directionHi := (249979908371144108541/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree026.table
  base := (-3564979557501589674339003163848368674251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-34923230397183504560067059611495137000000000000)
      constant := (214692479972566991937116381806317372259491327061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree026.table
  base := (-715988874639179152524403993518936286329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-131249388326971216693595745139533000000000000)
      constant := (809005711814328374453512433858362527288447355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/5000000000000000000)
  centralHi := (249979908371144108541/100000000000000000000)
  directionLo := (50986097231624006123/20000000000000000000)
  directionHi := (31866310769765003827/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree027.table
  base := (-27588027335826760839243278757661759/38146972656250000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (75617350998465432435555186968750000000000000)
      linear := (-2014838155977758125662371497275771500000000000)
      constant := (12896165317179326530458613250677640683970333696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree027.table
  base := (-1452008459451709008266297038001456920943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (125976428152378896185847875000000000000000)
      linear := (-3365429576682115548479263994186000000000000)
      constant := (21598187688231924927775610521131118562829485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50986097231624006123/20000000000000000000)
  centralHi := (31866310769765003827/12500000000000000000)
  directionLo := (64946685325535115363/25000000000000000000)
  directionHi := (259786741302140461453/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree028.table
  base := (-7279292586522119055353305351237584396787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4695768)
      previous := (2347884)
      next := (2347884)
      square := (55555604815199093217958912875000000000000000)
      linear := (-1535140539510848488317482215936026000000000000)
      constant := (10216512231538591192894325438700689259003048893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree028.table
  base := (-3652732045166208362830189417596929932269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-141350407384280142733224638389533000000000000)
      constant := (943215451051966700375177203391256489733831531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64946685325535115363/25000000000000000000)
  centralHi := (259786741302140461453/100000000000000000000)
  directionLo := (132276934062552149927/50000000000000000000)
  directionHi := (52910773625020859971/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree029.table
  base := (-181890628346273261057000011194329166411/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-19477399814215964832816970814950693500000000000)
      constant := (134604054372749623681994316583715830662059888210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree029.table
  base := (-7300051050176161192280495621946107712971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-292801833825869211506078170029066000000000000)
      constant := (2028906327942459635736312889092920198305171229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132276934062552149927/50000000000000000000)
  centralHi := (52910773625020859971/20000000000000000000)
  directionLo := (16827287563137415663/6250000000000000000)
  directionHi := (269236601010198650609/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree030.table
  base := (-903067750223713107732292199456865255369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (75617350998465432435555186968750000000000000)
      linear := (-2238814224380448409304976053853896500000000000)
      constant := (16046503671158657038719568179858610348289885502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree030.table
  base := (-3623655922635826044951392577655423500533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (566893926685705032836315437500000000000000)
      linear := (-16827936271287674308094836848837000000000000)
      constant := (120935838433476321137593549003543243807919563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16827287563137415663/6250000000000000000)
  centralHi := (269236601010198650609/100000000000000000000)
  directionLo := (136919634737950134899/50000000000000000000)
  directionHi := (273839269475900269799/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree031.table
  base := (-7129203859578181867959835053794108504533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-83285024898528426138690392617677774000000000000)
      constant := (618374579190436659075230744711599305228391114763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree031.table
  base := (-3575203219215752552372092045639707424157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-156501935970243531792667978264533000000000000)
      constant := (1165108111444374694315427594764858227535837243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136919634737950134899/50000000000000000000)
  centralHi := (273839269475900269799/100000000000000000000)
  directionLo := (139182922525237044073/50000000000000000000)
  directionHi := (278365845050474088147/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree032.table
  base := (-1748114628434344424923336332585579749807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-21493184429840177385600411824153818500000000000)
      constant := (165127528112197220585684212647311235069556884977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree032.table
  base := (-7012181223215336366412438284277099437981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-323104890997795989624964849779066000000000000)
      constant := (2488991823697708662512541294371512148408348219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139182922525237044073/50000000000000000000)
  centralHi := (278365845050474088147/100000000000000000000)
  directionLo := (282819981391404475093/100000000000000000000)
  directionHi := (141409990695702237547/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree033.table
  base := (-6816872155675994601673351247258136922389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (211288)
      previous := (105644)
      next := (105644)
      square := (2499747140445138262332402875000000000000000)
      linear := (-81414555133326898940415887948166000000000000)
      constant := (646532619048962437955145982215411213249344011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree033.table
  base := (-3417600203037346818457234159205507765091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (396)
      previous := (198)
      next := (198)
      square := (4685073774262025064762937500000000000000)
      linear := (-152987102871948997091181700197000000000000)
      constant := (1218157374858595033290317891618150430114181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282819981391404475093/100000000000000000000)
  centralHi := (141409990695702237547/50000000000000000000)
  directionLo := (143602524401387350529/50000000000000000000)
  directionHi := (287205048802774701059/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree034.table
  base := (-6604757364602708580313170055875286289079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-91348163361025276349824156654490274000000000000)
      constant := (749060261601611742987949286771040394568094318569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree034.table
  base := (-165544353229209758436750766240255556123/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-85826732278103460426055659069766500000000000)
      constant := (705664599354596204567698394305903552944384770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143602524401387350529/50000000000000000000)
  centralHi := (287205048802774701059/100000000000000000000)
  directionLo := (145762082038997732889/50000000000000000000)
  directionHi := (291524164077995465779/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree035.table
  base := (-1271639651434137732607935901082580824221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4695768)
      previous := (2347884)
      next := (2347884)
      square := (55555604815199093217958912875000000000000000)
      linear := (-1919099513915460403133375741498526000000000000)
      constant := (16233946561301552421142225131620197023193716095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree035.table
  base := (-398373982796164674314319186841224231659/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-88351987042430691935962882382266500000000000)
      constant := (749376582372374321513088537863529145222040564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145762082038997732889/50000000000000000000)
  centralHi := (291524164077995465779/100000000000000000000)
  directionLo := (295780216419124026061/100000000000000000000)
  directionHi := (147890108209562013031/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree036.table
  base := (-6079073104983510540675012546773260848991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-10747065444743315906360740668040586000000000000)
      constant := (93697607861634687795305908520485431484890285689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree036.table
  base := (-6093704422770151590330642281738251723217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (125976428152378896185847875000000000000000)
      linear := (-4487765027494218441771363244186000000000000)
      constant := (39230520734892309877268564089405671541490743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295780216419124026061/100000000000000000000)
  centralHi := (147890108209562013031/50000000000000000000)
  directionLo := (37496986255671616281/12500000000000000000)
  directionHi := (299975890045372930249/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree037.table
  base := (-5769074691829795364683438131971322827509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-99411301823522126560957920691302774000000000000)
      constant := (892501103251268621503400764554103021887463320299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree037.table
  base := (-5782625784939314299352517383021895364203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-373609986284340619823109316029066000000000000)
      constant := (3363139388134734123048250986311544403535446397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37496986255671616281/12500000000000000000)
  centralHi := (299975890045372930249/100000000000000000000)
  directionLo := (304113683993475529437/100000000000000000000)
  directionHi := (152056841996737764719/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree038.table
  base := (-1085945729186730245663497992851508115167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-102099014644354409964669175370240274000000000000)
      constant := (943127289950109697706673420962573852489310559685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree038.table
  base := (-217690804059938617266720308897571217309/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-383711005341649545862738209279066000000000000)
      constant := (3553893035348105146025712364182280612478862275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304113683993475529437/100000000000000000000)
  centralHi := (152056841996737764719/50000000000000000000)
  directionLo := (154097964762398239969/50000000000000000000)
  directionHi := (308195929524796479939/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree039.table
  base := (-253120497693794215328040900410116199151/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (75617350998465432435555186968750000000000000)
      linear := (-2910742429588519260232789723588271500000000000)
      constant := (27643150991359651034741925587988020408532261645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree039.table
  base := (-5074008959146875624757282578951871758393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-43756891599884274655818566947674000000000000)
      constant := (416657742027238957497021631750107411655110023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154097964762398239969/50000000000000000000)
  centralHi := (308195929524796479939/100000000000000000000)
  directionLo := (312224805483521989159/100000000000000000000)
  directionHi := (7805620137088049729/2500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree040.table
  base := (-933671567888250876964352324005099024341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-107474440286018976772091684728115274000000000000)
      constant := (1048576300282983290356958919746112618185724275255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree040.table
  base := (-1169769541121033152622522616360833330259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-100978260864066849485498998944766500000000000)
      constant := (987801801171346994507660636460707472530131541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312224805483521989159/100000000000000000000)
  centralHi := (7805620137088049729/2500000000000000000)
  directionLo := (39525293986650372653/12500000000000000000)
  directionHi := (12648094075728119249/4000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree041.table
  base := (-531086146361506829649011530988463018961/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-27540538276712815043950734851763193500000000000)
      constant := (275848240867264347487087344225533371734831763742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree041.table
  base := (-425859118778535031149194597417426413389/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-207007031256788161990812444514533000000000000)
      constant := (2078872350773325418071201637969562018611872055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525293986650372653/12500000000000000000)
  centralHi := (12648094075728119249/4000000000000000000)
  directionLo := (320130482032503101559/100000000000000000000)
  directionHi := (8003262050812577539/2500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree042.table
  base := (-3804410543103977289245730589515650917973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (521752)
      previous := (260876)
      next := (260876)
      square := (6172844979466565913106545875000000000000000)
      linear := (-255895387591119146438807696340114000000000000)
      constant := (2629480256949253531055072660999024705707338083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree042.table
  base := (-238346954665867750540800452344672528219/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (283446963342852516418157718750000000000000)
      linear := (-11780974488080145833923716174418500000000000)
      constant := (121375620444966130741679844344013606467078036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320130482032503101559/100000000000000000000)
  centralHi := (8003262050812577539/2500000000000000000)
  directionLo := (8100274829825706881/2500000000000000000)
  directionHi := (324010993193028275241/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree043.table
  base := (-667285833206263123336862957419096074337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-115537578748515826983225448764927774000000000000)
      constant := (1217197417747785360967020879008910412522439319035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree043.table
  base := (-3344862358015964503979331943952081515193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-434216100628194176060882675529066000000000000)
      constant := (4586531248655167601614388655174063649069593407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8100274829825706881/2500000000000000000)
  centralHi := (324010993193028275241/100000000000000000000)
  directionLo := (327845576290884912539/100000000000000000000)
  directionHi := (16392278814544245627/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree044.table
  base := (-2845562677705309649110461750074298863687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (1901592)
      previous := (950796)
      next := (950796)
      square := (22497724264006244360991625875000000000000000)
      linear := (-977068525366513308982947962345994000000000000)
      constant := (10546947924788304019023051624982330475854587617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree044.table
  base := (-1426669444770463105857859466507431263121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (3564)
      previous := (1782)
      next := (1782)
      square := (42165663968358225582866437500000000000000)
      linear := (-1836021155725219430167403176773000000000000)
      constant := (19870923376095042868967515121824898067687199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327845576290884912539/100000000000000000000)
  centralHi := (16392278814544245627/5000000000000000000)
  directionLo := (66327164895560631421/20000000000000000000)
  directionHi := (165817912238901578553/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree045.table
  base := (-2332547988142023716832355952116547128223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-13434778265575599310071995346978086000000000000)
      constant := (148505412219878454441315885532129268611761525817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree045.table
  base := (-467942939526885165742945520872024650999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (125976428152378896185847875000000000000000)
      linear := (-5610100478306321335063462494186000000000000)
      constant := (62175453936371298561010747091742425086145605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66327164895560631421/20000000000000000000)
  centralHi := (165817912238901578553/50000000000000000000)
  directionLo := (335383240876228172683/100000000000000000000)
  directionHi := (83845810219057043171/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree046.table
  base := (-224756156243314190199203598380736203719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-30900179302753169298589803200435068500000000000)
      constant := (349574928608459627872361423670582324722468343218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree046.table
  base := (-902325484231842227170405417163763962139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-232259578900060477089884677639533000000000000)
      constant := (2634434851931383547537356608690795949407075661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335383240876228172683/100000000000000000000)
  centralHi := (83845810219057043171/25000000000000000000)
  directionLo := (169544622772451789729/50000000000000000000)
  directionHi := (339089245544903579459/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree047.table
  base := (-1242665041894773979399995447175908035533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-126288430031844960598070467480677774000000000000)
      constant := (1461432147166840823483661353851884425194480255763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree047.table
  base := (-624371718440079633208882183807067456051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-237310088428714940109699124264533000000000000)
      constant := (2753365711633898488694407873119607931863244149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169544622772451789729/50000000000000000000)
  centralHi := (339089245544903579459/100000000000000000000)
  directionLo := (85688795441623279429/25000000000000000000)
  directionHi := (342755181766493117717/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree048.table
  base := (-666934843229681636106706376823884709537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-14330682539186360444642413573290586000000000000)
      constant := (169549399734163438702409358707647476190300601223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree048.table
  base := (-26901154619255388263620299393575928111/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-53857910657193200695447460197674000000000000)
      constant := (638865740694549599480179583014961895357178025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85688795441623279429/25000000000000000000)
  centralHi := (342755181766493117717/100000000000000000000)
  directionLo := (21648895108511705121/6250000000000000000)
  directionHi := (346382321736187281937/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree049.table
  base := (-14268973743494814832569514707984308067/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-54837091076013963933982914135174000000000000)
      constant := (662988669077604317794793044571141025442575185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree049.table
  base := (-122385411671874304591613861869387941/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-494822214972047732298656035029066000000000000)
      constant := (5998045692773917226790444168268320330493911875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/6250000000000000000)
  centralHi := (346382321736187281937/100000000000000000000)
  directionLo := (87492967929900437989/25000000000000000000)
  directionHi := (349971871719601751957/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree050.table
  base := (106184896955577194783263615924835043/1953125000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-33587892123585452702301057879372568500000000000)
      constant := (414776147982390086870741861852546649247595682560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree050.table
  base := (538934759417221639128095582936858344711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-504923234029356658338284928279066000000000000)
      constant := (6251489232018988522633865805426664148636512511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87492967929900437989/25000000000000000000)
  centralHi := (349971871719601751957/100000000000000000000)
  directionLo := (176762488369627796933/50000000000000000000)
  directionHi := (353524976739255593867/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree051.table
  base := (73606552297442767333685771981582053579/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (75617350998465432435555186968750000000000000)
      linear := (-3806646703199280394803207949900771500000000000)
      constant := (47993054371555584178365311269475622549151298636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree051.table
  base := (36667357563284050779695917084638008837/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (283446963342852516418157718750000000000000)
      linear := (-14306229252407377343830939486918500000000000)
      constant := (180836623220576919300245469553409866332987944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176762488369627796933/50000000000000000000)
  centralHi := (353524976739255593867/100000000000000000000)
  directionLo := (178521362420622530437/50000000000000000000)
  directionHi := (2856341798729960487/800000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree052.table
  base := (1830413675003304901589484600854032087577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-139726994136006377616626740875365274000000000000)
      constant := (1797770960097881570691592871554647526305034618553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree052.table
  base := (1826417413524871300767997113070356826113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-525125272143974510417542714779066000000000000)
      constant := (6773929837415869589584119232948234567252733513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178521362420622530437/50000000000000000000)
  centralHi := (2856341798729960487/800000000000000000)
  directionLo := (360526150987179925893/100000000000000000000)
  directionHi := (180263075493589962947/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree053.table
  base := (1250736190961382264037747337382689151421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-71207353478419330510168997777151387000000000000)
      constant := (934583380644657839487601713292606392114639823069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree053.table
  base := (2497801940220675175634491584784054438373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-535226291201283436457171608029066000000000000)
      constant := (7042920312535336574456943330202866517550493773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360526150987179925893/100000000000000000000)
  centralHi := (180263075493589962947/50000000000000000000)
  directionLo := (181988120305420403853/50000000000000000000)
  directionHi := (363976240610840807707/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree054.table
  base := (3190591826522799631752143851143812716177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-16122491086407882713783250025915586000000000000)
      constant := (215770733884741338832705206020564220614116458217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree054.table
  base := (637444368050355675131777813211162944401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (125976428152378896185847875000000000000000)
      linear := (-6732435929118424228355561744186000000000000)
      constant := (90334407983083371660991417785236753581362605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181988120305420403853/50000000000000000000)
  centralHi := (363976240610840807707/100000000000000000000)
  directionLo := (367393932874197727139/100000000000000000000)
  directionHi := (18369696643709886357/5000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree055.table
  base := (1948755712377784178796962854123534162747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (950796)
      previous := (475398)
      next := (475398)
      square := (11248862132003122180495812937500000000000000)
      linear := (-610703027266542263751076466579247000000000000)
      constant := (8330908304841765349904745322288777949722799923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree055.table
  base := (778883672053079112241617591355390107317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (84331327936716451165732875000000000000000)
      linear := (-4590316771205795773028342103546000000000000)
      constant := (62780392592210814303474873846028932993463385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367393932874197727139/100000000000000000000)
  centralHi := (18369696643709886357/5000000000000000000)
  directionLo := (370780123653278277473/100000000000000000000)
  directionHi := (185390061826639138737/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree056.table
  base := (2310998160501135014540226445933357232157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2347884)
      previous := (1173942)
      next := (1173942)
      square := (27777802407599546608979456437500000000000000)
      linear := (-1535488218564648073790528159093013000000000000)
      constant := (21342813894306307226539975029804527875265129677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree056.table
  base := (4619158361267072190805775500792848149743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-565529348373210214576058287779066000000000000)
      constant := (7880939398623318204036398673175766704715631143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370780123653278277473/100000000000000000000)
  centralHi := (185390061826639138737/50000000000000000000)
  directionLo := (23383479267549109491/6250000000000000000)
  directionHi := (374135668280785751857/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree057.table
  base := (1072766969566753398440459096518911847567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-17018395360018643848353668252228086000000000000)
      constant := (240942656347678456173647794073267655944335062035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree057.table
  base := (2680615891521671507612491190850767013207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (566893926685705032836315437500000000000000)
      linear := (-31979464857251063367538176723837000000000000)
      constant := (453923370707057219532247118208495485277382423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23383479267549109491/6250000000000000000)
  centralHi := (374135668280785751857/100000000000000000000)
  directionLo := (188730692034629053551/50000000000000000000)
  directionHi := (377461384069258107103/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree058.table
  base := (6122836236574675560974009869678313173711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-155853271061000078038894268948990274000000000000)
      constant := (2246743747432214136468160555640425485993857240879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree058.table
  base := (6120449359580933145953244345235222250389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-585731386487828066655316074279066000000000000)
      constant := (8465469470972447666170297436944878413276062589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188730692034629053551/50000000000000000000)
  centralHi := (377461384069258107103/100000000000000000000)
  directionLo := (380758052635856674797/100000000000000000000)
  directionHi := (190379026317928337399/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree059.table
  base := (6898828553908651689410596018073237305111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-158540983881832361442605523627927774000000000000)
      constant := (2326374832999191222619656306107262385776063375479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree059.table
  base := (1724160140159122876007747699297257815419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-148958101386284248173736241882266500000000000)
      constant := (2191371030498164065970265962339460923848921619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380758052635856674797/100000000000000000000)
  centralHi := (190379026317928337399/50000000000000000000)
  directionLo := (76805284409503914361/20000000000000000000)
  directionHi := (192013211023759785903/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree060.table
  base := (7691656842207418768548257962513639247601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-17914299633629404982924086478540586000000000000)
      constant := (267486306518225693675433606594588334987852290121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree060.table
  base := (76896517370703361560555858376986518133/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (283446963342852516418157718750000000000000)
      linear := (-16831484016734608853738162799418500000000000)
      constant := (251962864440901047835651892514923457956170925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76805284409503914361/20000000000000000000)
  centralHi := (192013211023759785903/50000000000000000000)
  directionLo := (387267208803158869317/100000000000000000000)
  directionHi := (193633604401579434659/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree061.table
  base := (85011814434695204735751810578451601929/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-40979102380874232062507008246450693500000000000)
      constant := (622437289816123507002358284137449842014903377025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree061.table
  base := (8499344449773713360791436142549892217607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-616034443659754844774202754029066000000000000)
      constant := (9381005107770087145359660230312457493624766207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387267208803158869317/100000000000000000000)
  centralHi := (193633604401579434659/50000000000000000000)
  directionLo := (195240549833890343547/50000000000000000000)
  directionHi := (78096219933556137419/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree062.table
  base := (1865455297748133358114083560313019558577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-166604122344329211653739287664740274000000000000)
      constant := (2573491705692409353809039389398404156982980687765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree062.table
  base := (9325593964015730858993510660293514699181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-626135462717063770813831647279066000000000000)
      constant := (9696508863160507058676779599348228737566672981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195240549833890343547/50000000000000000000)
  centralHi := (78096219933556137419/20000000000000000000)
  directionLo := (39366875337182794853/10000000000000000000)
  directionHi := (393668753371827948531/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree063.table
  base := (10169828536677356991577505898852598491973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (521752)
      previous := (260876)
      next := (260876)
      square := (6172844979466565913106545875000000000000000)
      linear := (-383881712392656451377438871527614000000000000)
      constant := (6028580728648399600686715336634754056458907917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree063.table
  base := (508414394641756857446621556307040376147/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31494107038094724046461968750000000000000)
      linear := (-1963692844982631780411915248546500000000000)
      constant := (30917201495491019247118446300220259427568935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39366875337182794853/10000000000000000000)
  centralHi := (393668753371827948531/100000000000000000000)
  directionLo := (396830802187656449781/100000000000000000000)
  directionHi := (198415401093828224891/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree064.table
  base := (5514367673264284188489308592262051328101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-85989773992996889230580898511307637000000000000)
      constant := (1372543039430665793749699159607485438725021075589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree064.table
  base := (11027324974723047784549446902040807392317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-646337500831681622893089433779066000000000000)
      constant := (10342997379441788101072629421078325953252098917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396830802187656449781/100000000000000000000)
  centralHi := (198415401093828224891/50000000000000000000)
  directionLo := (12498995418557205427/3125000000000000000)
  directionHi := (79993570678766114733/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree065.table
  base := (1487988096533017651666093164051729619497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-43666815201706515466218262925388193500000000000)
      constant := (708234349335339998068857091619321833234145982866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree065.table
  base := (11902613972303195477652505322506977192999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-656438519888990548932718327029066000000000000)
      constant := (10673980253651075858003967750594680883468583199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/3125000000000000000)
  centralHi := (79993570678766114733/20000000000000000000)
  directionLo := (25192530664802725793/6250000000000000000)
  directionHi := (403080490636843612689/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree066.table
  base := (511810150635551711616432810131703067861/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (211288)
      previous := (105644)
      next := (105644)
      square := (2499747140445138262332402875000000000000000)
      linear := (-162860398188850638446817544885666000000000000)
      constant := (2683340532258356015130061381657686476648356525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree066.table
  base := (12794072680032186119128774503492492855849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (792)
      previous := (396)
      next := (396)
      square := (9370147548524050129525875000000000000000)
      linear := (-612065692329016965080208650394000000000000)
      constant := (10110304041754290818362696716735432435702641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25192530664802725793/6250000000000000000)
  centralHi := (403080490636843612689/100000000000000000000)
  directionLo := (203084637599455313583/50000000000000000000)
  directionHi := (406169275198910627167/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree067.table
  base := (3425676869790407159758512204442145808087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-45010671612122657168073890264856943500000000000)
      constant := (753186802505107143996067436951298275530801189943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree067.table
  base := (13701627030127888547658895593292538954987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-676640558003608401011976113529066000000000000)
      constant := (11351419196961495963139565306763382174297827587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203084637599455313583/50000000000000000000)
  centralHi := (406169275198910627167/100000000000000000000)
  directionLo := (81846949435926619553/20000000000000000000)
  directionHi := (204617373589816548883/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree068.table
  base := (7313099227002679596402102932755583202977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-91365199634661456038003407869182637000000000000)
      constant := (1552352666066351984309630662939629404089408729153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree068.table
  base := (14625210287002366137017151836705607671857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-686741577060917327051605006779066000000000000)
      constant := (11697873886048798276958095247392439660791870457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81846949435926619553/20000000000000000000)
  centralHi := (204617373589816548883/50000000000000000000)
  directionLo := (206138713299290317851/50000000000000000000)
  directionHi := (412277426598580635703/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree069.table
  base := (3113133178569737398510874978176247281907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-20602012454461688386635341157478086000000000000)
      constant := (355336894111048331133266654788467191682934517735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree069.table
  base := (15564762321438290813900002203071675354339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-77426955124247361454581544447674000000000000)
      constant := (1338831619933985623356235393418951054460875171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206138713299290317851/50000000000000000000)
  centralHi := (412277426598580635703/100000000000000000000)
  directionLo := (415297814425163894353/100000000000000000000)
  directionHi := (207648907212581947177/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree070.table
  base := (16521055001009877839947343088589009227351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4695768)
      previous := (2347884)
      next := (2347884)
      square := (55555604815199093217958912875000000000000000)
      linear := (-3838894385938519977212843369311026000000000000)
      constant := (67198514517338163710517741241701643121380676711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree070.table
  base := (16520228956615032707329271246552594104283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-706943615175535179130862793279066000000000000)
      constant := (12406250746045693969518178089353081974816077683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415297814425163894353/100000000000000000000)
  centralHi := (207648907212581947177/50000000000000000000)
  directionLo := (83659278708314881619/20000000000000000000)
  directionHi := (13071762298174200253/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree071.table
  base := (17492316394008719711533552739011428286131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-190793537731819762287140579775177774000000000000)
      constant := (3388790696058051912371788308496422681414035578259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree071.table
  base := (17491561378872022842769814878186321804599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-717044634232844105170491686529066000000000000)
      constant := (12768171907545581118374854945924090140006874799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83659278708314881619/20000000000000000000)
  centralHi := (13071762298174200253/3125000000000000000)
  directionLo := (8425472592880651377/2000000000000000000)
  directionHi := (421273629644032568851/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree072.table
  base := (18479405563396333169919162657217206458003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-21497916728072449521205759383790586000000000000)
      constant := (387358042749903217749041887871260492037385489563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree072.table
  base := (9239357803400520049571797217498276965029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (62988214076189448092923937500000000000000)
      linear := (-4488553415371315007469880122093000000000000)
      constant := (81081775511381173343015205268813291512768509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8425472592880651377/2000000000000000000)
  centralHi := (421273629644032568851/100000000000000000000)
  directionLo := (1325718662772208477/312500000000000000)
  directionHi := (424229972087106712641/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree073.table
  base := (19482282395325221843244952714037776926221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-196168963373484329094563089133052774000000000000)
      constant := (3585022172537565367483095155457830122913443860269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree073.table
  base := (1948165201289343382529824934154627294589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-368623336173730978624874736514533000000000000)
      constant := (6753738766775494287033529363112106510571333945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1325718662772208477/312500000000000000)
  centralHi := (424229972087106712641/100000000000000000000)
  directionLo := (42716585467543770511/10000000000000000000)
  directionHi := (427165854675437705111/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree074.table
  base := (20500910736652386787430743198447034451797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-198856676194316612498274343811990274000000000000)
      constant := (3685189964894135820830844741337436629063734646133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree074.table
  base := (20500334892539858921417601159690148759189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-747347691404770883289378366279066000000000000)
      constant := (13884861259726420404547342999081207147988811389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42716585467543770511/10000000000000000000)
  centralHi := (427165854675437705111/100000000000000000000)
  directionLo := (53760212050852340377/12500000000000000000)
  directionHi := (430081696406818723017/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree075.table
  base := (21535258003882443843500533558419987559517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-22393821001683210655776177610103086000000000000)
      constant := (420747297402570373030375216508087808205778438357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree075.table
  base := (21534732075695086788216794562452082303957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-84160967829119978814334139947674000000000000)
      constant := (1585266499563492476389747245006560317629009173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53760212050852340377/12500000000000000000)
  centralHi := (430081696406818723017/100000000000000000000)
  directionLo := (21648895108511705121/5000000000000000000)
  directionHi := (432977902170234102421/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree076.table
  base := (112926474153605194864605433021610977901/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-51058025458995294826424213292466318500000000000)
      constant := (972407307735207789636008336437440742809849389450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree076.table
  base := (352887727765382249820332030392950620757/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-191887432379847183842159038194766500000000000)
      constant := (3663772239625091811152565317363054944544629712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/5000000000000000000)
  centralHi := (432977902170234102421/100000000000000000000)
  directionLo := (87170972680429954517/20000000000000000000)
  directionHi := (217927431701074886293/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree077.table
  base := (1478187171901654032864591690803302264467/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (9702)
      previous := (4851)
      next := (4851)
      square := (114784307469419614086691968750000000000000)
      linear := (-8724903637072586553778382014201500000000000)
      constant := (168405319558312144367073364953255025194519788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree077.table
  base := (23650556280446667012101357006139367455179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (84331327936716451165732875000000000000000)
      linear := (-6426865690716509598415413603546000000000000)
      constant := (124363077611989159868857676377639288763869499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87170972680429954517/20000000000000000000)
  centralHi := (217927431701074886293/50000000000000000000)
  directionLo := (438712958704067073523/100000000000000000000)
  directionHi := (109678239676016768381/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree078.table
  base := (98929335638095024840939886474603381477/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (151234701996930864871110373937500000000000000)
      linear := (-11644862637646985895173297918207793000000000000)
      constant := (227752199853667429342228912487066247623759939625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree078.table
  base := (24731933655484092928499312535523697574847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-87527974181556287494210437697674000000000000)
      constant := (1716214284788778719972252548058357306659008383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438712958704067073523/100000000000000000000)
  centralHi := (109678239676016768381/25000000000000000000)
  directionLo := (3449629331438267919/781250000000000000)
  directionHi := (441552554424098293633/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree079.table
  base := (12914645404892383492822201681969196913991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-106147620149239014758415308603338887000000000000)
      constant := (2103273145446449620019365055008555218009846213799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree079.table
  base := (12914462750465814310585542715387471598059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-398926393345657756743761416264533000000000000)
      constant := (7924538633426354188905345756554469609132576259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3449629331438267919/781250000000000000)
  centralHi := (441552554424098293633/100000000000000000000)
  directionLo := (444374005205093100251/100000000000000000000)
  directionHi := (111093501301273275063/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree080.table
  base := (26941846075683439091842587647011069992303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-214982953119310312920541871885615274000000000000)
      constant := (4314920588564612499006331265456406647587104738767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree080.table
  base := (26941512714460346871827965497488081610551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-807953805748624439527151725779066000000000000)
      constant := (16257378315089862222646586934830160687865010351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444374005205093100251/100000000000000000000)
  centralHi := (111093501301273275063/25000000000000000000)
  directionLo := (447177654501637563577/100000000000000000000)
  directionHi := (223588827250818781789/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree081.table
  base := (28069982244811035599832427259771428798667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-24185629548904732924917014062728086000000000000)
      constant := (491629160524709496345642377775904221266017535507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree081.table
  base := (7017419521202052892306701330952412103429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (31494107038094724046461968750000000000000)
      linear := (-2524860570388683227057964873546500000000000)
      constant := (51453183762724971599789089845386741864514909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447177654501637563577/100000000000000000000)
  centralHi := (223588827250818781789/50000000000000000000)
  directionLo := (112490958767014848843/25000000000000000000)
  directionHi := (449963835068059395373/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree082.table
  base := (14606841789492214213807758570854856671707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-110179189380487439863982190621745137000000000000)
      constant := (2267885909107881919685244092934022635836088904123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree082.table
  base := (29213406104578133311623653574266056089973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-828155843863242291606409512279066000000000000)
      constant := (17089436786963795231639433571295393615737825373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112490958767014848843/25000000000000000000)
  centralHi := (449963835068059395373/100000000000000000000)
  directionLo := (452732869419402308849/100000000000000000000)
  directionHi := (9054657388388046177/2000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree083.table
  base := (3796616986750544581341986344609965537637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-55761522895451790782918908980606943500000000000)
      constant := (1162062167989369458609536694106305464113277099786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree083.table
  base := (30372682801567400585427413130302557402471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-838256862920551217646038405529066000000000000)
      constant := (17513193921671016747025185976141473365101618271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452732869419402308849/100000000000000000000)
  centralHi := (9054657388388046177/2000000000000000000)
  directionLo := (18219402810687090419/4000000000000000000)
  directionHi := (113871267566794315119/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree084.table
  base := (31547726406222287923282877964886065721829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (521752)
      previous := (260876)
      next := (260876)
      square := (6172844979466565913106545875000000000000000)
      linear := (-511868037194193756316070046715114000000000000)
      constant := (10798396763089030056514195799219835483664724141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree084.table
  base := (985859237087314162624576949088630839909/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (283446963342852516418157718750000000000000)
      linear := (-23565496721607226213490758299418500000000000)
      constant := (498391744996109532019431938359314151877287208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18219402810687090419/4000000000000000000)
  centralHi := (113871267566794315119/25000000000000000000)
  directionLo := (114555185232889292003/25000000000000000000)
  directionHi := (458220740931557168013/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree085.table
  base := (32738043594256318671000902009507279969159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-228421517223471729939098145280302774000000000000)
      constant := (4877304689785286572749662159227074120355280376551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree085.table
  base := (32737833117567355641866090546499539649099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-858458901035169069725296192029066000000000000)
      constant := (18376163370360862549777739385622351988100819299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114555185232889292003/25000000000000000000)
  centralHi := (458220740931557168013/100000000000000000000)
  directionLo := (460940175731553101511/100000000000000000000)
  directionHi := (57617521966444137689/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree086.table
  base := (33943877074360401778449253369853776082067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-231109230044304013342809399959240274000000000000)
      constant := (4993883796596284219732627658402136588930243682163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree086.table
  base := (16971842587056571596932867042748985402327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (5102045340171345295526838937500000000000000)
      linear := (-434279960046238997882462542639533000000000000)
      constant := (9407687736504884174992042033317720805928206927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460940175731553101511/100000000000000000000)
  centralHi := (57617521966444137689/12500000000000000000)
  directionLo := (23182183017729633079/5000000000000000000)
  directionHi := (463643660354592661581/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree087.table
  base := (17582608744049432990237794973131762749349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (151234701996930864871110373937500000000000000)
      linear := (-12988719048063127597028925257676543000000000000)
      constant := (283990570471436466055947051820495091345703620829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree087.table
  base := (35165042548412232924459507265046663054363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-97628993238865213533839330947674000000000000)
      constant := (2139971004173207171263054957556173816066201307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23182183017729633079/5000000000000000000)
  centralHi := (463643660354592661581/100000000000000000000)
  directionLo := (233165736103407088459/50000000000000000000)
  directionHi := (466331472206814176919/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree088.table
  base := (4550257050138910790678342347590109519009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54022500000000000000000000000000000000000000
      center := (475398)
      previous := (237699)
      next := (237699)
      square := (5624431066001561090247906468750000000000000)
      linear := (-488604660508199545764941961398998500000000000)
      constant := (10808148932646226560777906816485492353192530962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree088.table
  base := (4550237118005364676434524740135412375323/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (1782)
      previous := (891)
      next := (891)
      square := (21082831984179112791433218750000000000000)
      linear := (-1836285037617966627777237338386500000000000)
      constant := (40721599137799425556783617746513936804802326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233165736103407088459/50000000000000000000)
  centralHi := (466331472206814176919/100000000000000000000)
  directionLo := (234501940372646238431/50000000000000000000)
  directionHi := (469003880745292476863/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree089.table
  base := (37654386211872719446629021115486427648741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-239172368506800863553943163996052774000000000000)
      constant := (5351825221465412366314542923194941678022458956549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree089.table
  base := (37654240885938236881779932610996256138919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-898862977264404773883811765029066000000000000)
      constant := (20163920235154809361594908484945948306417545119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234501940372646238431/50000000000000000000)
  centralHi := (469003880745292476863/100000000000000000000)
  directionLo := (471661147793322437757/100000000000000000000)
  directionHi := (235830573896661218879/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree090.table
  base := (38922200069462428374733058232595708100911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-26873342369737016328628268741665586000000000000)
      constant := (608208184974082825652833760791789552713184764631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree090.table
  base := (38922067639076556045495660950187555311693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (125976428152378896185847875000000000000000)
      linear := (-11221777732366835801523958744186000000000000)
      constant := (254614046036155304570695576988712694192714853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471661147793322437757/100000000000000000000)
  centralHi := (235830573896661218879/50000000000000000000)
  directionLo := (474303527839804471837/100000000000000000000)
  directionHi := (237151763919902235919/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree091.table
  base := (2010274589972582928292744770464514899897/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 133402500000000000000000000000000000000000000
      center := (1173942)
      previous := (586971)
      next := (586971)
      square := (13888901203799773304489728218750000000000000)
      linear := (-1247692827288088930415130986499631500000000000)
      constant := (28557598965104907669947940190216207647867019085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree091.table
  base := (10051342783805282119436885407263815085719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-229766253844755656490767387882266500000000000)
      constant := (5272176601135361135916840655514169151655131919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474303527839804471837/100000000000000000000)
  centralHi := (237151763919902235919/50000000000000000000)
  directionLo := (95386253664740183011/20000000000000000000)
  directionHi := (29808204270231307191/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree092.table
  base := (41504255837108843579691124740376048530283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (2722224635944755567679986730875000000000000000)
      linear := (-247235506969297713765076928032865274000000000000)
      constant := (5722072404096819368893189736351529667955597126987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree092.table
  base := (1297004559590995950163554225636564301519/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-232291508609082888000674611194766500000000000)
      constant := (5389706552101706925213959953658129733753501752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95386253664740183011/20000000000000000000)
  centralHi := (29808204270231307191/6250000000000000000)
  directionLo := (239772304952231620333/50000000000000000000)
  directionHi := (479544609904463240667/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree093.table
  base := (42818487167199765238252038039708750709797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-27769246643347777463198686967978086000000000000)
      constant := (649802519162471120548010499136227073964960934237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree093.table
  base := (10704596756997859816568914440732524859959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (283446963342852516418157718750000000000000)
      linear := (-26090751485934457723397981611918500000000000)
      constant := (612058252562318361870687819789153219572495351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239772304952231620333/50000000000000000000)
  centralHi := (479544609904463240667/100000000000000000000)
  directionLo := (482143786719266608649/100000000000000000000)
  directionHi := (9642875734385332173/2000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree094.table
  base := (22074090634865762586265642131506328229751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-126305466305481140286249718695370137000000000000)
      constant := (2987870095219224169991475848950156190352719412439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree094.table
  base := (44148090060018778222773100242878688951267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-949368072550949404081956231279066000000000000)
      constant := (22514519012550183725063907566842858030411367867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482143786719266608649/100000000000000000000)
  centralHi := (9642875734385332173/2000000000000000000)
  directionLo := (484729026627829945521/100000000000000000000)
  directionHi := (242364513313914972761/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree095.table
  base := (22746667035526736972859981814069061683677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (1361112317972377783839993365437500000000000000)
      linear := (-127649322715897281988105346034838887000000000000)
      constant := (3052312473687057295560240464005923373324631731453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree095.table
  base := (45493251003987318793638167266037942020721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-959469091608258330121585124529066000000000000)
      constant := (23000091930132732416330135515174207869745086521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484729026627829945521/100000000000000000000)
  centralHi := (242364513313914972761/50000000000000000000)
  directionLo := (243650275722773037323/50000000000000000000)
  directionHi := (487300551445546074647/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree096.table
  base := (1874157675991447431117074919683843856763/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (302469403993861729742220747875000000000000000)
      linear := (-28665150916958538597769105194290586000000000000)
      constant := (692764103741080382103520470278434206027766088075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree096.table
  base := (46853866256822726327400819323128192082279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (1133787853371410065672630875000000000000000)
      linear := (-107730012296174139573468224197674000000000000)
      constant := (2610090645519708394136043055574790601177601831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243650275722773037323/50000000000000000000)
  centralHi := (487300551445546074647/100000000000000000000)
  directionLo := (244929288582798484759/50000000000000000000)
  directionHi := (489858577165596969519/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree097.table
  base := (6028750180887723498253798081428362329627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (680556158986188891919996682718750000000000000)
      linear := (-65168517768364782695908300356888193500000000000)
      constant := (1591624035168429760454650751441041106042580182006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree097.table
  base := (1205748314304676364463547411223627870393/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (2551022670085672647763419468750000000000000)
      linear := (-244917782430719045550210727757266500000000000)
      constant := (5996672654841688726648582558755153267577217930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell077.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244929288582798484759/50000000000000000000)
  centralHi := (489858577165596969519/100000000000000000000)
  directionLo := (492403314170683608417/100000000000000000000)
  directionHi := (246201657085341804209/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree098.table
  base := (4962150973092601941552785108132791486651/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (566893926685705032836315437500000000000000)
      linear := (-54844186566907833025269566036337000000000000)
      constant := (1353494910576614875459690103047196549644814695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree098.table
  base := (49621447025163011529313757300740238921633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (10204090680342690591053677875000000000000000)
      linear := (-989772148780185108240471804279066000000000000)
      constant := (24487716330533756115374019086916423081670925033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell077.Kernel098
