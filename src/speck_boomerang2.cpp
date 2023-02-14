#include "ortools_extend_sat.h"
#include "bct_entry.hpp"

#include <iostream>
#include <vector>
#include <array>
#include <tuple>

using std::cout;
using std::endl;

using namespace operations_research;
using namespace operations_research::sat;

static std::vector< BoolVec > intermediate;
static std::vector< BoolVar > interBits;

template<int branchSize>
constexpr int getAlpha() { return branchSize == 16 ? 7 : 8; }

template<int branchSize>
constexpr int getBeta() { return branchSize == 16 ? 2 : 3; }

static void BVRor(CpModelBuilder &model, BoolVec &output, BoolVec &bv0, const int rotation)
{
    const int len = bv0.size();
    const int rn = rotation % len;

    for (int i = rn; i < len; ++i) {
        model.AddEquality(output[i - rn], bv0[i]);
    }
    for (int i = 0; i < rn; ++i) {
        model.AddEquality(output[i + (len - rn)], bv0[i]);
    }

    return;
} 

static void BVRol(CpModelBuilder &model, BoolVec &output, BoolVec &bv0, const int rotation)
{
    const int len = bv0.size();
    const int rn = rotation % len;
    BVRor(model, output, bv0, len - rn);

    return;
} 

template<int branchSize>
static void printm(const std::vector<int> &state)
{
    for (int i = 0; i < 2; ++i) {
        cout << "0b";
        for (int j = 0; j < branchSize; ++j)
            cout << state[i * branchSize + branchSize - 1 - j];
        cout << " | ";
    }
    cout << endl;
    return;
}

template<int branchSize>
static void addAddition_SAT_MILP(CpModelBuilder &model, BoolVec &a, BoolVec &b, BoolVec &output, IntVar &prob)
{
    const std::vector<std::array<int, 8>> eqs{
        {  0,  1, -1,  0,  0,  0,  1,  0 },
        {  1, -1,  0,  0,  0,  0,  1,  0 },
        { -1,  0,  1,  0,  0,  0,  1,  0 },
        { -1, -1, -1,  0,  0,  0, -1, -3 },
        {  1,  1,  1,  0,  0,  0, -1,  0 },
        {  0, -1,  0,  1,  1,  1,  1,  0 },
        {  0,  1,  0,  1, -1,  1,  1,  0 },
        {  0,  1,  0, -1,  1,  1,  1,  0 },
        {  1,  0,  0,  1,  1, -1,  1,  0 },
        {  0,  0,  1, -1, -1, -1,  1, -2 },
        {  0, -1,  0,  1, -1, -1,  1, -2 },
        {  0, -1,  0, -1,  1, -1,  1, -2 },
        {  0, -1,  0, -1, -1,  1,  1, -2 }
    };

    std::vector<std::vector<int64_t>> table2;
    for (int i = 0b000; i <= 0b111; ++i) {
        const int a = (i >> 0) & 1;
        const int b = (i >> 1) & 1;
        const int c = (i >> 2) & 1;
        const int d = a ^ b ^ c;
        table2.push_back({ a, b, c, d, 1 });
    }
    for (int i = 0b0000; i <= 0b1111; ++i) {
        const int a = (i >> 0) & 1;
        const int b = (i >> 1) & 1;
        const int c = (i >> 2) & 1;
        const int d = (i >> 3) & 1;
        table2.push_back({ a, b, c, d, 0 });
    }

    std::vector<BoolVar> equals;

    model.AddBoolXor({ a[0], b[0], output[0], model.TrueVar() });
    for (int i = 0; i < branchSize - 1; ++i) {
        const int eqsSize = eqs.size();
        auto isEqual = model.NewBoolVar();

        for (int j = 0; j < eqsSize; ++j) {
            model.AddGreaterOrEqual(LinearExpr::BooleanScalProd({ a[i],      b[i],      output[i], a[i + 1],  b[i + 1],  output[i + 1], isEqual.Not() },
                                                                { eqs[j][0], eqs[j][1], eqs[j][2], eqs[j][3], eqs[j][4], eqs[j][5],     eqs[j][6] }),
                                    eqs[j][7]);
        }

        auto literal1 = model.NewBoolVar();
        auto literal2 = model.NewBoolVar();
        //model.AddBoolAnd({ a[i - 1], b[i - 1], output[i - 1] }).OnlyEnforceIf(literal1);
        //model.AddBoolOr({ Not(a[i - 1]), Not(b[i - 1]), Not(output[i - 1]) }).OnlyEnforceIf(Not(literal1));
        //model.AddBoolAnd({ Not(a[i - 1]), Not(b[i - 1]), Not(output[i - 1]) }).OnlyEnforceIf(literal2);
        //model.AddBoolOr({ a[i - 1], b[i - 1], output[i - 1] }).OnlyEnforceIf(Not(literal2));
        //model.AddBoolOr({ literal1, literal2 }).OnlyEnforceIf(isEqual);
        //model.AddBoolAnd({ Not(literal1), Not(literal2) }).OnlyEnforceIf(Not(isEqual));

        model.AddGreaterOrEqual(isEqual, literal1);
        model.AddGreaterOrEqual(isEqual, literal2);
        model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literal1, literal2 }), isEqual);

        model.AddGreaterOrEqual(a[i], literal1);
        model.AddGreaterOrEqual(b[i], literal1);
        model.AddGreaterOrEqual(output[i], literal1);
        model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literal1, model.TrueVar(), model.TrueVar() }), LinearExpr::BooleanSum({ a[i], b[i], output[i] }));

        model.AddGreaterOrEqual(a[i].Not(), literal2);
        model.AddGreaterOrEqual(b[i].Not(), literal2);
        model.AddGreaterOrEqual(output[i].Not(), literal2);
        model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literal2, a[i], b[i], output[i] }), model.TrueVar());

        std::vector<BoolVar> tmp1 = { a[i + 1], b[i + 1], output[i + 1], a[i] };
        std::vector<BoolVar> tmp2 = { a[i + 1], b[i + 1], output[i + 1], b[i] };
        std::vector<BoolVar> tmp3 = { a[i + 1], b[i + 1], output[i + 1], output[i] };
        BVAssignIf(model, tmp1, table2, isEqual);
        BVAssignIf(model, tmp2, table2, isEqual);
        BVAssignIf(model, tmp3, table2, isEqual);

        equals.push_back(isEqual);
    }

    model.AddEquality(prob, LinearExpr::BooleanSum(equals));
    return;
}

template<int branchSize>
static void onlyLargeSwitch_BCT_new(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, const int halfNum = 1)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
        {{0, 0, 0, 0, 1, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 1},
  {0, 1, 0, 0, 1, 1, 0, 0, 1},
  {1, 1, 0, 0, 1, 1, 0, 0, 1},
  {0, 0, 1, 0, 1, 0, 1, 0, 1},
  {1, 0, 1, 0, 1, 0, 0, 1, 1},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 1, 0, 1},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 1, 1},
  {0, 0, 1, 1, 1, 0, 1, 0, 1},
  {1, 0, 1, 1, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 1, 1},
  {1, 1, 1, 1, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 1, 1, 0, 0, 1},
  {1, 0, 0, 0, 1, 1, 0, 0, 1},
  {0, 1, 0, 0, 1, 1, 0, 0, 1},
  {1, 1, 0, 0, 0, 1, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 1, 0, 1},
  {1, 1, 1, 0, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 0, 1, 1, 0, 1},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 1, 0, 1},
  {0, 1, 1, 1, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 1, 1}},
 {{0, 0, 0, 0, 1, 0, 1, 0, 1},
  {1, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 1, 0, 1},
  {1, 1, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 1, 0, 1},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 1, 0, 1},
  {0, 0, 0, 1, 1, 0, 1, 0, 1},
  {1, 0, 0, 1, 0, 1, 1, 0, 1},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 1, 0, 0},
  {1, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 1, 1, 1, 0, 0, 1, 1, 1},
  {1, 1, 1, 1, 0, 0, 1, 1, 1}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 1, 1},
  {0, 1, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 1, 1},
  {0, 0, 1, 0, 1, 0, 0, 1, 1},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 1, 1},
  {1, 1, 0, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 0, 0, 1, 1, 1},
  {1, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 1, 1, 1, 0, 0, 1, 1, 1},
  {1, 1, 1, 1, 0, 0, 0, 1, 0}}};

    //{
    //    {{0, 0, 0, 0, 1, 0, 0, 0, 1},
    //     {1, 0, 0, 0, 1, 1, 0, 0, 1},
    //     {0, 1, 0, 0, 1, 1, 0, 0, 1},
    //     {1, 1, 0, 0, 1, 1, 0, 0, 1},
    //     {0, 0, 1, 0, 1, 0, 1, 0, 1},
    //     {1, 0, 1, 0, 1, 0, 0, 1, 1},
    //     {0, 1, 1, 0, 0, 0, 0, 0, 0},
    //     {1, 1, 1, 0, 0, 0, 0, 0, 0},
    //     {0, 0, 0, 1, 1, 0, 1, 0, 1},
    //     {1, 0, 0, 1, 0, 0, 0, 0, 0},
    //     {0, 1, 0, 1, 0, 0, 0, 0, 0},
    //     {1, 1, 0, 1, 1, 0, 0, 1, 1},
    //     {0, 0, 1, 1, 1, 0, 1, 0, 1},
    //     {1, 0, 1, 1, 0, 0, 0, 0, 0},
    //     {0, 1, 1, 1, 1, 0, 0, 1, 1},
    //     {1, 1, 1, 1, 0, 0, 0, 0, 0}},
    //    {{0, 0, 0, 0, 1, 1, 0, 0, 1},
    //     {1, 0, 0, 0, 1, 1, 0, 0, 1},
    //     {0, 1, 0, 0, 1, 1, 0, 0, 1},
    //     {1, 1, 0, 0, 0, 1, 0, 0, 1},
    //     {0, 0, 1, 0, 0, 0, 0, 0, 0},
    //     {1, 0, 1, 0, 0, 0, 0, 0, 0},
    //     {0, 1, 1, 0, 0, 1, 1, 0, 1},
    //     {1, 1, 1, 0, 0, 1, 0, 1, 1},
    //     {0, 0, 0, 1, 0, 1, 1, 0, 1},
    //     {1, 0, 0, 1, 0, 0, 0, 0, 0},
    //     {0, 1, 0, 1, 0, 0, 0, 0, 0},
    //     {1, 1, 0, 1, 0, 1, 0, 1, 1},
    //     {0, 0, 1, 1, 0, 0, 0, 0, 0},
    //     {1, 0, 1, 1, 0, 1, 1, 0, 1},
    //     {0, 1, 1, 1, 0, 0, 0, 0, 0},
    //     {1, 1, 1, 1, 0, 1, 0, 1, 1}},
    //    {{0, 0, 0, 0, 1, 0, 1, 0, 1},
    //     {1, 0, 0, 0, 0, 0, 0, 0, 0},
    //     {0, 1, 0, 0, 0, 1, 1, 0, 1},
    //     {1, 1, 0, 0, 0, 0, 0, 0, 0},
    //     {0, 0, 1, 0, 1, 0, 1, 0, 1},
    //     {1, 0, 1, 0, 0, 0, 0, 0, 0},
    //     {0, 1, 1, 0, 0, 0, 0, 0, 0},
    //     {1, 1, 1, 0, 0, 1, 1, 0, 1},
    //     {0, 0, 0, 1, 1, 0, 1, 0, 1},
    //     {1, 0, 0, 1, 0, 1, 1, 0, 1},
    //     {0, 1, 0, 1, 0, 0, 0, 0, 0},
    //     {1, 1, 0, 1, 0, 0, 0, 0, 0},
    //     {0, 0, 1, 1, 0, 0, 1, 0, 1},
    //     {1, 0, 1, 1, 0, 0, 1, 1, 1},
    //     {0, 1, 1, 1, 0, 0, 1, 1, 1},
    //     {1, 1, 1, 1, 0, 0, 1, 1, 1}},
    //    {{0, 0, 0, 0, 0, 0, 0, 0, 0},
    //     {1, 0, 0, 0, 1, 0, 0, 1, 1},
    //     {0, 1, 0, 0, 0, 0, 0, 0, 0},
    //     {1, 1, 0, 0, 0, 1, 0, 1, 1},
    //     {0, 0, 1, 0, 1, 0, 0, 1, 1},
    //     {1, 0, 1, 0, 0, 0, 0, 0, 0},
    //     {0, 1, 1, 0, 0, 0, 0, 0, 0},
    //     {1, 1, 1, 0, 0, 1, 0, 1, 1},
    //     {0, 0, 0, 1, 0, 0, 0, 0, 0},
    //     {1, 0, 0, 1, 0, 0, 0, 0, 0},
    //     {0, 1, 0, 1, 1, 0, 0, 1, 1},
    //     {1, 1, 0, 1, 0, 1, 0, 1, 1},
    //     {0, 0, 1, 1, 0, 0, 1, 1, 1},
    //     {1, 0, 1, 1, 0, 0, 1, 1, 1},
    //     {0, 1, 1, 1, 0, 0, 1, 1, 1},
    //     {1, 1, 1, 1, 0, 0, 0, 1, 1}}
    //};

    std::array< std::array<BoolVar, 4>, branchSize > dp;
    std::array< std::array<BoolVar, 4>, branchSize > can0;
    std::array< BoolVar, branchSize > isHalf;

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 4; ++j) {
            dp[i][j] = model.NewBoolVar();
            can0[i][j] = model.NewBoolVar();
        }
    for (int i = 0; i < branchSize; ++i)
        isHalf[i] = model.NewBoolVar();
    model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    model.AddEquality(can0[0][0], model.FalseVar());
    model.AddEquality(can0[0][1], model.TrueVar());
    model.AddEquality(can0[0][2], model.TrueVar());
    model.AddEquality(can0[0][3], model.TrueVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 16);
        for (int cn = 0; cn < 4; ++cn) {
            auto halfSize = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(matrix[0 * 4 + cn]);
            column.push_back(matrix[1 * 4 + cn]);
            column.push_back(matrix[2 * 4 + cn]);
            column.push_back(matrix[3 * 4 + cn]);
            column.push_back(halfSize);
            BVAssign(model, column, table[cn]);

            std::array<BoolVar, 4> literals;
            for (int li = 0; li < 4; ++li) literals[li] = model.NewBoolVar();
            for (int r = 0; r < 4; ++r) {
                model.AddBoolAnd({ dp[i][cn], matrix[r * 4 + cn], can0[i + 1][r] }).OnlyEnforceIf(literals[r]);
                model.AddBoolOr({ Not(dp[i][cn]), Not(matrix[r * 4 + cn]), Not(can0[i + 1][r]) }).OnlyEnforceIf(Not(literals[r]));

                // milp
                model.AddGreaterOrEqual(dp[i][cn], literals[r]);
                model.AddGreaterOrEqual(matrix[r * 4 + cn], literals[r]);
                model.AddGreaterOrEqual(can0[i + 1][r], literals[r]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r], model.TrueVar(), model.TrueVar() }), LinearExpr::BooleanSum({ dp[i][cn], matrix[r * 4 + cn], can0[i + 1][r] }));
                // milp
            }
            model.AddLessOrEqual(LinearExpr::BooleanSum(literals), halfSize);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        std::array<BoolVar, 4> ifEnforced;
        for (int j = 0; j < 4; ++j) {
            ifEnforced[j] = model.NewBoolVar();
            model.AddBoolAnd({ isHalf[i], can0[i][j] }).OnlyEnforceIf(ifEnforced[j]);
            model.AddBoolOr({ Not(isHalf[i]), Not(can0[i][j]) }).OnlyEnforceIf(Not(ifEnforced[j]));
            model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), matrix[j * 4 + j] });
            model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), dp[i + 1][j] });

            // milp
            model.AddGreaterOrEqual(isHalf[i],  ifEnforced[j]);
            model.AddGreaterOrEqual(can0[i][j], ifEnforced[j]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], model.TrueVar() }), LinearExpr::BooleanSum({ isHalf[i], can0[i][j] }));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], Not(dp[i][j]), matrix[j * 4 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }
        /*
        model.AddEquality(matrix[0 * 4 + 0], model.TrueVar()).OnlyEnforceIf(dp[i][0]);
        model.AddEquality(matrix[1 * 4 + 1], model.TrueVar()).OnlyEnforceIf(dp[i][1]);
        model.AddEquality(matrix[2 * 4 + 2], model.TrueVar()).OnlyEnforceIf(dp[i][2]);
        model.AddEquality(matrix[3 * 4 + 3], model.TrueVar()).OnlyEnforceIf(dp[i][3]);

        model.AddEquality(dp[i + 1][0], model.TrueVar()).OnlyEnforceIf(dp[i][0]);
        model.AddEquality(dp[i + 1][1], model.TrueVar()).OnlyEnforceIf(dp[i][1]);
        model.AddEquality(dp[i + 1][2], model.TrueVar()).OnlyEnforceIf(dp[i][2]);
        model.AddEquality(dp[i + 1][3], model.TrueVar()).OnlyEnforceIf(dp[i][3]);
        */

        auto literals = NewBoolVec(model, 16);
        for (int r = 0; r < 4; ++r) {
            for (int c = 0; c < 4; ++c) {
                model.AddBoolAnd({ matrix[r * 4 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 4 + c]);
                model.AddBoolOr({ Not(matrix[r * 4 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 4 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 4 + c],  literals[r * 4 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 4 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 4 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 4 + 0]), Not(literals[r * 4 + 1]), Not(literals[r * 4 + 2]), Not(literals[r * 4 + 3]) }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 4; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 4 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }), dp[i + 1][r]);
            // milp
        }
    }

    return;
}

template<int branchSize>
static void onlyLargeSwitch_UBCT(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, BoolVec &dLL, const int halfNum)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
       {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 1, 1, 0, 0, 1},
       {0, 0, 1, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 1, 0, 0, 1, 1},
       {0, 0, 1, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 1, 1, 0, 0, 1},
       {0, 1, 0, 0, 1, 1, 1, 0, 0, 1},
       {1, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 1, 0, 0, 1, 1},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 1, 0, 0, 1, 1},
       {1, 1, 1, 1, 1, 0, 0, 0, 0, 0}},
      {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 1, 1, 0, 0, 1},
       {0, 1, 0, 0, 0, 1, 1, 0, 0, 1},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 1, 1, 0, 1},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 0, 0, 1, 1, 0, 1},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 1, 1, 0, 0, 1},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 1, 0, 1, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 0, 1, 1, 0, 1, 1, 0, 1},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 1, 0, 1, 0, 1, 1}},
      {{0, 0, 0, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 1, 1, 0, 1},
       {0, 0, 0, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 1, 0, 0},
       {1, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 1, 1, 1},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 1, 1, 0, 1},
       {1, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 1, 1, 0, 1},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 1, 1, 1},
       {0, 1, 1, 1, 1, 0, 0, 1, 1, 1},
       {1, 1, 1, 1, 1, 0, 0, 0, 0, 0}},
      {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 1, 0, 0, 1, 1},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 1, 0, 0, 1, 1},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 0, 0, 0, 1, 1, 1},
       {0, 1, 1, 1, 0, 0, 0, 1, 1, 1},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 0, 1, 1, 0, 0, 1, 1},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 1, 1, 0, 0, 1, 1, 1},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 1, 0, 0, 0, 1, 0}}};

    const std::vector< std::vector<int64_t> > lastTable{
        { 0, 0, 0, 1, 0, 1, 0 },
        { 1, 0, 0, 0, 1, 0, 1 },
        { 0, 1, 0, 0, 1, 0, 1 },
        { 1, 1, 0, 1, 0, 1, 0 },
        { 0, 0, 1, 0, 1, 0, 1 },
        { 1, 0, 1, 1, 0, 1, 0 },
        { 0, 1, 1, 1, 0, 1, 0 },
        { 1, 1, 1, 0, 1, 0, 1 }
    };

    std::array< std::array<BoolVar, 4>, branchSize > dp;
    std::array< std::array<BoolVar, 4>, branchSize > can0;
    std::array< BoolVar, branchSize > isHalf;

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 4; ++j) {
            dp[i][j] = model.NewBoolVar();
            can0[i][j] = model.NewBoolVar();
        }
    for (int i = 0; i < branchSize; ++i)
        isHalf[i] = model.NewBoolVar();
    model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    model.AddEquality(can0[0][0], model.FalseVar());
    model.AddEquality(can0[0][1], model.TrueVar());
    model.AddEquality(can0[0][2], model.TrueVar());
    model.AddEquality(can0[0][3], model.TrueVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 16);
        for (int cn = 0; cn < 4; ++cn) {
            auto halfSize = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(dLL[i]);
            column.push_back(matrix[0 * 4 + cn]);
            column.push_back(matrix[1 * 4 + cn]);
            column.push_back(matrix[2 * 4 + cn]);
            column.push_back(matrix[3 * 4 + cn]);
            column.push_back(halfSize);
            BVAssign(model, column, table[cn]);

            std::array<BoolVar, 4> literals;
            for (int li = 0; li < 4; ++li) literals[li] = model.NewBoolVar();
            for (int r = 0; r < 4; ++r) {
                model.AddBoolAnd({ dp[i][cn], matrix[r * 4 + cn], can0[i + 1][r] }).OnlyEnforceIf(literals[r]);
                model.AddBoolOr({ Not(dp[i][cn]), Not(matrix[r * 4 + cn]), Not(can0[i + 1][r]) }).OnlyEnforceIf(Not(literals[r]));

                // milp
                model.AddGreaterOrEqual(dp[i][cn], literals[r]);
                model.AddGreaterOrEqual(matrix[r * 4 + cn], literals[r]);
                model.AddGreaterOrEqual(can0[i + 1][r], literals[r]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r], model.TrueVar(), model.TrueVar() }), LinearExpr::BooleanSum({ dp[i][cn], matrix[r * 4 + cn], can0[i + 1][r] }));
                // milp
            }
            model.AddLessOrEqual(LinearExpr::BooleanSum(literals), halfSize);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        std::array<BoolVar, 4> ifEnforced;
        for (int j = 0; j < 4; ++j) {
            ifEnforced[j] = model.NewBoolVar();
            model.AddBoolAnd({ isHalf[i], can0[i][j] }).OnlyEnforceIf(ifEnforced[j]);
            model.AddBoolOr({ Not(isHalf[i]), Not(can0[i][j]) }).OnlyEnforceIf(Not(ifEnforced[j]));
            model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), matrix[j * 4 + j] });
            model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), dp[i + 1][j] });

            // milp
            model.AddGreaterOrEqual(isHalf[i],  ifEnforced[j]);
            model.AddGreaterOrEqual(can0[i][j], ifEnforced[j]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], model.TrueVar() }), LinearExpr::BooleanSum({ isHalf[i], can0[i][j] }));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], Not(dp[i][j]), matrix[j * 4 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }

        auto literals = NewBoolVec(model, 16);
        for (int r = 0; r < 4; ++r) {
            for (int c = 0; c < 4; ++c) {
                model.AddBoolAnd({ matrix[r * 4 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 4 + c]);
                model.AddBoolOr({ Not(matrix[r * 4 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 4 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 4 + c],  literals[r * 4 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 4 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 4 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 4 + 0]), Not(literals[r * 4 + 1]), Not(literals[r * 4 + 2]), Not(literals[r * 4 + 3]) }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 4; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 4 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }), dp[i + 1][r]);
            // milp
        }
    }

    // last validation
    std::vector<BoolVar> isValid;
    isValid.push_back(dL[branchSize - 1]);
    isValid.push_back(dR[branchSize - 1]);
    isValid.push_back(dLL[branchSize - 1]);
    for (int i = 0; i < 4; ++i) isValid.push_back(model.NewBoolVar());
    BVAssign(model, isValid, lastTable);

    for (int i = 0; i < 4; ++i)
        model.AddBoolOr({ Not(dp[branchSize - 1][i]), can0[branchSize - 1][i], isValid[3 + i] });

    return;
}

template<int branchSize>
static void onlyLargeSwitch_LBCT(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, BoolVec &nLL, const int halfNum)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0},
         {1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0},
         {1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0},
         {1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0},
         {1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}}
    };

    const std::vector< std::vector<int64_t> > lastTable{
        { 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1 }
    };

    std::array< std::array<BoolVar, 8>, branchSize > dp;
    std::array< std::array<BoolVar, 8>, branchSize > can0;
    std::array< BoolVar, branchSize > isHalf;

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 8; ++j) {
            dp[i][j] = model.NewBoolVar();
            can0[i][j] = model.NewBoolVar();
        }

    //for (int i = 0; i < 8; ++i) {
    //    BoolVec tmp;
    //    for (int j = 0; j < branchSize; ++j)
    //        tmp.push_back(can0[j][i]);
    //    intermediate.push_back(tmp);
    //}
    
    for (int i = 0; i < branchSize; ++i) {
        isHalf[i] = model.NewBoolVar();
    }
    model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    model.AddEquality(dp[0][4], model.FalseVar());
    model.AddEquality(dp[0][5], model.FalseVar());
    model.AddEquality(dp[0][6], model.FalseVar());
    model.AddEquality(dp[0][7], model.FalseVar());
    model.AddEquality(can0[0][0], model.FalseVar());
    model.AddEquality(can0[0][1], model.TrueVar());
    model.AddEquality(can0[0][2], model.TrueVar());
    model.AddEquality(can0[0][3], model.TrueVar());
    model.AddEquality(can0[0][4], model.TrueVar());
    model.AddEquality(can0[0][5], model.TrueVar());
    model.AddEquality(can0[0][6], model.TrueVar());
    model.AddEquality(can0[0][7], model.TrueVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 64);
        for (int cn = 0; cn < 8; ++cn) {
            auto halfSize0 = model.NewBoolVar();
            auto halfSize1 = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(nLL[i]);
            column.push_back(matrix[0 * 8 + cn]);
            column.push_back(matrix[1 * 8 + cn]);
            column.push_back(matrix[2 * 8 + cn]);
            column.push_back(matrix[3 * 8 + cn]);
            column.push_back(matrix[4 * 8 + cn]);
            column.push_back(matrix[5 * 8 + cn]);
            column.push_back(matrix[6 * 8 + cn]);
            column.push_back(matrix[7 * 8 + cn]);
            column.push_back(halfSize0);
            column.push_back(halfSize1);
            BVAssign(model, column, table[cn]);

            std::array<BoolVar, 8> literals;
            for (int li = 0; li < 8; ++li) literals[li] = model.NewBoolVar();
            for (int r = 0; r < 8; ++r) {
                model.AddBoolAnd({ dp[i][cn], matrix[r * 8 + cn], can0[i + 1][r] }).OnlyEnforceIf(literals[r]);
                model.AddBoolOr({ Not(dp[i][cn]), Not(matrix[r * 8 + cn]), Not(can0[i + 1][r]) }).OnlyEnforceIf(Not(literals[r]));

                // milp
                model.AddGreaterOrEqual(dp[i][cn], literals[r]);
                model.AddGreaterOrEqual(matrix[r * 8 + cn], literals[r]);
                model.AddGreaterOrEqual(can0[i + 1][r], literals[r]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r], model.TrueVar(), model.TrueVar() }), LinearExpr::BooleanSum({ dp[i][cn], matrix[r * 8 + cn], can0[i + 1][r] }));
                // milp
            }
            model.AddLessOrEqual(LinearExpr::BooleanSum(literals), LinearExpr::BooleanSum({ halfSize0, halfSize1 }));
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3], dp[i + 1][4], dp[i + 1][5], dp[i + 1][6], dp[i + 1][7] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        std::array<BoolVar, 8> ifEnforced;
        for (int j = 0; j < 8; ++j) {
            ifEnforced[j] = model.NewBoolVar();
            model.AddBoolAnd({ isHalf[i], can0[i][j] }).OnlyEnforceIf(ifEnforced[j]);
            model.AddBoolOr({ Not(isHalf[i]), Not(can0[i][j]) }).OnlyEnforceIf(Not(ifEnforced[j]));
            model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), matrix[j * 8 + j] });
            model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), dp[i + 1][j] });

            // milp
            model.AddGreaterOrEqual(isHalf[i],  ifEnforced[j]);
            model.AddGreaterOrEqual(can0[i][j], ifEnforced[j]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], model.TrueVar() }), LinearExpr::BooleanSum({ isHalf[i], can0[i][j] }));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], Not(dp[i][j]), matrix[j * 8 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }
        /*
        model.AddEquality(matrix[0 * 4 + 0], model.TrueVar()).OnlyEnforceIf(dp[i][0]);
        model.AddEquality(matrix[1 * 4 + 1], model.TrueVar()).OnlyEnforceIf(dp[i][1]);
        model.AddEquality(matrix[2 * 4 + 2], model.TrueVar()).OnlyEnforceIf(dp[i][2]);
        model.AddEquality(matrix[3 * 4 + 3], model.TrueVar()).OnlyEnforceIf(dp[i][3]);

        model.AddEquality(dp[i + 1][0], model.TrueVar()).OnlyEnforceIf(dp[i][0]);
        model.AddEquality(dp[i + 1][1], model.TrueVar()).OnlyEnforceIf(dp[i][1]);
        model.AddEquality(dp[i + 1][2], model.TrueVar()).OnlyEnforceIf(dp[i][2]);
        model.AddEquality(dp[i + 1][3], model.TrueVar()).OnlyEnforceIf(dp[i][3]);
        */

        auto literals = NewBoolVec(model, 64);
        for (int r = 0; r < 8; ++r) {
            for (int c = 0; c < 8; ++c) {
                model.AddBoolAnd({ matrix[r * 8 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 8 + c]);
                model.AddBoolOr({ Not(matrix[r * 8 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 8 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 8 + c],  literals[r * 8 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 8 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 8 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                              literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7]
                            }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 8 + 0]), Not(literals[r * 8 + 1]), Not(literals[r * 8 + 2]), Not(literals[r * 8 + 3]),
                               Not(literals[r * 8 + 4]), Not(literals[r * 8 + 5]), Not(literals[r * 8 + 6]), Not(literals[r * 8 + 7])
                             }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 8; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 8 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                                                             literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7],
                                                           }), dp[i + 1][r]);
            // milp
        }
    }

    // last validation
    std::vector<BoolVar> isValid;
    isValid.push_back(nL[branchSize - 1]);
    isValid.push_back(nR[branchSize - 1]);
    isValid.push_back(nLL[branchSize - 1]);
    for (int i = 0; i < 8; ++i) isValid.push_back(model.NewBoolVar());
    BVAssign(model, isValid, lastTable);

    for (int i = 0; i < 8; ++i)
        model.AddBoolOr({ Not(dp[branchSize - 1][i]), can0[branchSize - 1][i], isValid[3 + i] });

    return;
}

template<int branchSize>
static void onlyLargeSwitch_LBCT_enum(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, BoolVec &nLL, const int halfNum)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0},
         {1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0},
         {1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0},
         {1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0},
         {1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}}
    };

    const std::vector< std::vector<int64_t> > lastTable{
        { 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1 }
    };

    std::array< std::array<BoolVar, 8>, branchSize > dp;
    //std::array< BoolVar, branchSize > isHalf;
    auto isHalf = NewBoolVec(model, branchSize - 1);
    //intermediate.push_back(isHalf);

    /*
    {
        BoolVec tmp;
        for (int i = 0; i < branchSize; ++i) tmp.push_back(isHalf[i]);
        intermediate.push_back(tmp);
    }
    */

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 8; ++j) {
            dp[i][j] = model.NewBoolVar();
        }

    //for (int i = 0; i < 8; ++i) {
    //    BoolVec tmp;
    //    for (int j = 0; j < branchSize; ++j)
    //        tmp.push_back(can0[j][i]);
    //    intermediate.push_back(tmp);
    //}
    
    //for (int i = 0; i < branchSize; ++i) {
    //    isHalf[i] = model.NewBoolVar();
    //}
    model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    model.AddEquality(dp[0][4], model.FalseVar());
    model.AddEquality(dp[0][5], model.FalseVar());
    model.AddEquality(dp[0][6], model.FalseVar());
    model.AddEquality(dp[0][7], model.FalseVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 64);
        for (int cn = 0; cn < 8; ++cn) {
            auto halfSize0 = model.NewBoolVar();
            auto halfSize1 = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(nLL[i]);
            column.push_back(matrix[0 * 8 + cn]);
            column.push_back(matrix[1 * 8 + cn]);
            column.push_back(matrix[2 * 8 + cn]);
            column.push_back(matrix[3 * 8 + cn]);
            column.push_back(matrix[4 * 8 + cn]);
            column.push_back(matrix[5 * 8 + cn]);
            column.push_back(matrix[6 * 8 + cn]);
            column.push_back(matrix[7 * 8 + cn]);
            column.push_back(halfSize0);
            column.push_back(halfSize1);
            BVAssign(model, column, table[cn]);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3], dp[i + 1][4], dp[i + 1][5], dp[i + 1][6], dp[i + 1][7] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        auto ifEnforced = model.NewBoolVar();
        model.AddEquality(Not(isHalf[i]), ifEnforced);
        for (int j = 0; j < 8; ++j) {
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 8 + j] });
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] });

            //model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), Not(matrix[j * 8 + j]) });

            // milp
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 8 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }

        /*
        not(ifEnforced) => Or ( dp[i][j] and not(matrix[j * 4 + j]) )
        */
        auto enforcedLiterals = NewBoolVec(model, 8);
        for (int j = 0; j < 8; ++j) {
            model.AddBoolAnd({ Not(matrix[j * 8 + j]), dp[i][j] }).OnlyEnforceIf(enforcedLiterals[j]);
            model.AddBoolOr({ matrix[j * 8 + j], Not(dp[i][j]) }).OnlyEnforceIf(Not(enforcedLiterals[j]));
        }
        model.AddBoolOr({ ifEnforced, enforcedLiterals[0], enforcedLiterals[1], enforcedLiterals[2], enforcedLiterals[3],
                                      enforcedLiterals[4], enforcedLiterals[5], enforcedLiterals[6], enforcedLiterals[7] });

        auto literals = NewBoolVec(model, 64);
        for (int r = 0; r < 8; ++r) {
            for (int c = 0; c < 8; ++c) {
                model.AddBoolAnd({ matrix[r * 8 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 8 + c]);
                model.AddBoolOr({ Not(matrix[r * 8 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 8 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 8 + c],  literals[r * 8 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 8 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 8 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                              literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7]
                            }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 8 + 0]), Not(literals[r * 8 + 1]), Not(literals[r * 8 + 2]), Not(literals[r * 8 + 3]),
                               Not(literals[r * 8 + 4]), Not(literals[r * 8 + 5]), Not(literals[r * 8 + 6]), Not(literals[r * 8 + 7])
                             }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 8; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 8 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                                                             literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7],
                                                           }), dp[i + 1][r]);
            // milp
        }
    }

    // last validation
    std::vector<BoolVar> isValid;
    isValid.push_back(nL[branchSize - 1]);
    isValid.push_back(nR[branchSize - 1]);
    isValid.push_back(nLL[branchSize - 1]);
    for (int i = 0; i < 8; ++i) isValid.push_back(model.NewBoolVar());
    BVAssign(model, isValid, lastTable);

    auto lastLiterals = NewBoolVec(model, 8);
    for (int i = 0; i < 8; ++i) {
        model.AddBoolAnd({ dp[branchSize - 1][i], isValid[3 + i] }).OnlyEnforceIf(lastLiterals[i]);
        model.AddBoolOr({ Not(dp[branchSize - 1][i]), Not(isValid[3 + i]) }).OnlyEnforceIf(Not(lastLiterals[i]));
    }
    model.AddBoolOr({ lastLiterals[0], lastLiterals[1], lastLiterals[2], lastLiterals[3],
                      lastLiterals[4], lastLiterals[5], lastLiterals[6], lastLiterals[7] });

    return;
}

template<int branchSize>
static void onlyLargeSwitch_UBCT_enum(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, BoolVec &dLL, const int halfNum)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
       {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 1, 1, 0, 0, 1},
       {0, 0, 1, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 1, 0, 0, 1, 1},
       {0, 0, 1, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 1, 1, 0, 0, 1},
       {0, 1, 0, 0, 1, 1, 1, 0, 0, 1},
       {1, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 1, 0, 0, 1, 1},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 1, 0, 0, 1, 1},
       {1, 1, 1, 1, 1, 0, 0, 0, 0, 0}},
      {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 1, 1, 0, 0, 1},
       {0, 1, 0, 0, 0, 1, 1, 0, 0, 1},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 1, 1, 0, 1},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 0, 0, 1, 1, 0, 1},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 1, 1, 0, 0, 1},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 1, 0, 1, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 0, 1, 1, 0, 1, 1, 0, 1},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 1, 0, 1, 0, 1, 1}},
      {{0, 0, 0, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 1, 1, 0, 1},
       {0, 0, 0, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 1, 0, 0},
       {1, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 1, 1, 1},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 1, 1, 0, 1},
       {1, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 1, 1, 0, 1},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 1, 1, 1},
       {0, 1, 1, 1, 1, 0, 0, 1, 1, 1},
       {1, 1, 1, 1, 1, 0, 0, 0, 0, 0}},
      {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 1, 0, 0, 1, 1},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 1, 0, 0, 1, 1},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 0, 0, 0, 1, 1, 1},
       {0, 1, 1, 1, 0, 0, 0, 1, 1, 1},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 0, 1, 1, 0, 0, 1, 1},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 1, 1, 0, 0, 1, 1, 1},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 1, 0, 0, 0, 1, 0}}};

    const std::vector< std::vector<int64_t> > lastTable{
        { 0, 0, 0, 1, 0, 1, 0 },
        { 1, 0, 0, 0, 1, 0, 1 },
        { 0, 1, 0, 0, 1, 0, 1 },
        { 1, 1, 0, 1, 0, 1, 0 },
        { 0, 0, 1, 0, 1, 0, 1 },
        { 1, 0, 1, 1, 0, 1, 0 },
        { 0, 1, 1, 1, 0, 1, 0 },
        { 1, 1, 1, 0, 1, 0, 1 }
    };

    std::array< std::array<BoolVar, 4>, branchSize > dp;
    auto isHalf = NewBoolVec(model, branchSize - 1);

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 4; ++j) {
            dp[i][j] = model.NewBoolVar();
        }
    model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 16);
        for (int cn = 0; cn < 4; ++cn) {
            auto halfSize = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(dLL[i]);
            column.push_back(matrix[0 * 4 + cn]);
            column.push_back(matrix[1 * 4 + cn]);
            column.push_back(matrix[2 * 4 + cn]);
            column.push_back(matrix[3 * 4 + cn]);
            column.push_back(halfSize);
            BVAssign(model, column, table[cn]);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        auto ifEnforced = model.NewBoolVar();
        model.AddEquality(Not(isHalf[i]), ifEnforced);
        for (int j = 0; j < 4; ++j) {
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 4 + j] });
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] });

            // milp
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 4 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }

        auto enforcedLiterals = NewBoolVec(model, 4);
        for (int j = 0; j < 4; ++j) {
            model.AddBoolAnd({ Not(matrix[j * 4 + j]), dp[i][j] }).OnlyEnforceIf(enforcedLiterals[j]);
            model.AddBoolOr({ matrix[j * 4 + j], Not(dp[i][j]) }).OnlyEnforceIf(Not(enforcedLiterals[j]));
        }
        model.AddBoolOr({ ifEnforced, enforcedLiterals[0], enforcedLiterals[1], enforcedLiterals[2], enforcedLiterals[3] });

        auto literals = NewBoolVec(model, 16);
        for (int r = 0; r < 4; ++r) {
            for (int c = 0; c < 4; ++c) {
                model.AddBoolAnd({ matrix[r * 4 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 4 + c]);
                model.AddBoolOr({ Not(matrix[r * 4 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 4 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 4 + c],  literals[r * 4 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 4 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 4 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 4 + 0]), Not(literals[r * 4 + 1]), Not(literals[r * 4 + 2]), Not(literals[r * 4 + 3]) }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 4; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 4 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }), dp[i + 1][r]);
            // milp
        }
    }

    // last validation
    std::vector<BoolVar> isValid;
    isValid.push_back(dL[branchSize - 1]);
    isValid.push_back(dR[branchSize - 1]);
    isValid.push_back(dLL[branchSize - 1]);
    for (int i = 0; i < 4; ++i) isValid.push_back(model.NewBoolVar());
    BVAssign(model, isValid, lastTable);

    auto lastLiterals = NewBoolVec(model, 4);
    for (int i = 0; i < 4; ++i) {
        model.AddBoolAnd({ dp[branchSize - 1][i], isValid[3 + i] }).OnlyEnforceIf(lastLiterals[i]);
        model.AddBoolOr({ Not(dp[branchSize - 1][i]), Not(isValid[3 + i]) }).OnlyEnforceIf(Not(lastLiterals[i]));
    }
    model.AddBoolOr({ lastLiterals[0], lastLiterals[1], lastLiterals[2], lastLiterals[3] });

    return;
}

template<int branchSize>
static void onlyLargeSwitch_EBCT_enum(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, BoolVec &dLL, BoolVec &nLL, const int halfNum)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
        {{0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0},
  {0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
  {0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}}};

    const std::vector< std::vector<int64_t> > lastTable{
        {0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0}};

    std::array< std::array<BoolVar, 8>, branchSize > dp;
    //std::array< BoolVar, branchSize > isHalf;
    auto isHalf = NewBoolVec(model, branchSize - 1);

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 8; ++j) {
            dp[i][j] = model.NewBoolVar();
        }

    model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    model.AddEquality(dp[0][4], model.FalseVar());
    model.AddEquality(dp[0][5], model.FalseVar());
    model.AddEquality(dp[0][6], model.FalseVar());
    model.AddEquality(dp[0][7], model.FalseVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 64);
        for (int cn = 0; cn < 8; ++cn) {
            auto halfSize0 = model.NewBoolVar();
            auto halfSize1 = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(dLL[i]);
            column.push_back(nLL[i]);
            column.push_back(matrix[0 * 8 + cn]);
            column.push_back(matrix[1 * 8 + cn]);
            column.push_back(matrix[2 * 8 + cn]);
            column.push_back(matrix[3 * 8 + cn]);
            column.push_back(matrix[4 * 8 + cn]);
            column.push_back(matrix[5 * 8 + cn]);
            column.push_back(matrix[6 * 8 + cn]);
            column.push_back(matrix[7 * 8 + cn]);
            column.push_back(halfSize0);
            column.push_back(halfSize1);
            BVAssign(model, column, table[cn]);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3], dp[i + 1][4], dp[i + 1][5], dp[i + 1][6], dp[i + 1][7] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        auto ifEnforced = model.NewBoolVar();
        for (int j = 0; j < 8; ++j) {
            model.AddEquality(Not(isHalf[i]), ifEnforced);
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 8 + j] });
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] });

            //model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), Not(matrix[j * 8 + j]) });

            // milp
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 8 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }

        /*
        not(ifEnforced) => Or ( dp[i][j] and not(matrix[j * 4 + j]) )
        */
        auto enforcedLiterals = NewBoolVec(model, 8);
        for (int j = 0; j < 8; ++j) {
            model.AddBoolAnd({ Not(matrix[j * 8 + j]), dp[i][j] }).OnlyEnforceIf(enforcedLiterals[j]);
            model.AddBoolOr({ matrix[j * 8 + j], Not(dp[i][j]) }).OnlyEnforceIf(Not(enforcedLiterals[j]));
        }
        model.AddBoolOr({ ifEnforced, enforcedLiterals[0], enforcedLiterals[1], enforcedLiterals[2], enforcedLiterals[3],
                                      enforcedLiterals[4], enforcedLiterals[5], enforcedLiterals[6], enforcedLiterals[7] });

        auto literals = NewBoolVec(model, 64);
        for (int r = 0; r < 8; ++r) {
            for (int c = 0; c < 8; ++c) {
                model.AddBoolAnd({ matrix[r * 8 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 8 + c]);
                model.AddBoolOr({ Not(matrix[r * 8 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 8 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 8 + c],  literals[r * 8 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 8 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 8 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                              literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7]
                            }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 8 + 0]), Not(literals[r * 8 + 1]), Not(literals[r * 8 + 2]), Not(literals[r * 8 + 3]),
                               Not(literals[r * 8 + 4]), Not(literals[r * 8 + 5]), Not(literals[r * 8 + 6]), Not(literals[r * 8 + 7])
                             }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 8; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 8 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                                                             literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7],
                                                           }), dp[i + 1][r]);
            // milp
        }
    }

    // last validation
    std::vector<BoolVar> isValid;
    isValid.push_back(dL[branchSize - 1]);
    isValid.push_back(dR[branchSize - 1]);
    isValid.push_back(nL[branchSize - 1]);
    isValid.push_back(nR[branchSize - 1]);
    isValid.push_back(dLL[branchSize - 1]);
    isValid.push_back(nLL[branchSize - 1]);
    for (int i = 0; i < 8; ++i) isValid.push_back(model.NewBoolVar());
    BVAssign(model, isValid, lastTable);

    auto lastLiterals = NewBoolVec(model, 8);
    for (int i = 0; i < 8; ++i) {
        model.AddBoolAnd({ dp[branchSize - 1][i], isValid[6 + i] }).OnlyEnforceIf(lastLiterals[i]);
        model.AddBoolOr({ Not(dp[branchSize - 1][i]), Not(isValid[6 + i]) }).OnlyEnforceIf(Not(lastLiterals[i]));
    }
    model.AddBoolOr({ lastLiterals[0], lastLiterals[1], lastLiterals[2], lastLiterals[3],
                      lastLiterals[4], lastLiterals[5], lastLiterals[6], lastLiterals[7] });

    return;
}

template<int branchSize>
static void addRound(CpModelBuilder &model, std::array<BoolVec, 2> &state, std::array<BoolVec, 2> &output, IntVar &prob)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);
    auto afterAddition = NewBoolVec(model, branchSize);

    BVRor(model, afterAlpha, state[0], alpha);
    addAddition_SAT_MILP<branchSize>(model, afterAlpha, state[1], afterAddition, prob);

    BVRol(model, afterBeta, state[1], beta);
    BVXor(model, afterAddition, afterBeta, output[1]);

    for (int i = 0; i < branchSize; ++i)
        model.AddEquality(afterAddition[i], output[0][i]);

    return;
}

template<int branchSize>
static void _addSwitchUBCT(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, std::array<BoolVec, 2> &deltaOut, const int halfNum)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto beforeBeta = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);

    {
        intermediate.push_back(afterAlpha);
        intermediate.push_back(delta[1]);
        intermediate.push_back(nabla[0]);
        intermediate.push_back(beforeBeta);
        intermediate.push_back(deltaOut[0]);
    }

    BVRor(model, afterAlpha, delta[0], alpha);
    //onlyLargeSwitch_UBCT(model, afterAlpha, delta[1], nabla[0], beforeBeta, deltaOut[0], halfNum);
    onlyLargeSwitch_UBCT_enum<branchSize>(model, afterAlpha, delta[1], nabla[0], beforeBeta, deltaOut[0], halfNum);
    BVRol(model, afterBeta, beforeBeta, beta);
    BVXor(model, nabla[0], afterBeta, nabla[1]);

    // link deltaOut[1] to delta[1]
    auto tmp = NewBoolVec(model, branchSize);
    BVRol(model, tmp, delta[1], beta);
    BVXor(model, deltaOut[0], tmp, deltaOut[1]);
    return;
}

template<int branchSize>
static void _addSwitchLBCT(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, std::array<BoolVec, 2> &nablaIn, const int halfNum)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto beforeBeta = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);

    auto tmp1 = NewBoolVec(model, branchSize);
    BVRor(model, tmp1, nablaIn[0], alpha);

    {
        intermediate.push_back(afterAlpha);
        intermediate.push_back(delta[1]);
        intermediate.push_back(nabla[0]);
        intermediate.push_back(beforeBeta);
        intermediate.push_back(tmp1);
    }

    BVRor(model, afterAlpha, delta[0], alpha);
    //onlyLargeSwitch_LBCT(model, afterAlpha, delta[1], nabla[0], beforeBeta, tmp1, halfNum);
    onlyLargeSwitch_LBCT_enum<branchSize>(model, afterAlpha, delta[1], nabla[0], beforeBeta, tmp1, halfNum);
    BVRol(model, afterBeta, beforeBeta, beta);
    BVXor(model, nabla[0], afterBeta, nabla[1]);

    // link nablaIn[1] to nabla[1]
    auto tmp2 = NewBoolVec(model, branchSize);
    BVRol(model, tmp2, nablaIn[1], beta);
    BVXor(model, nabla[0], tmp2, nabla[1]);
    return;
}

template<int branchSize>
static void _addSwitchEBCT(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, std::array<BoolVec, 2> &deltaOut, std::array<BoolVec, 2> &nablaIn, const int halfNum)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto beforeBeta = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);

    auto tmp1 = NewBoolVec(model, branchSize);
    BVRor(model, tmp1, nablaIn[0], alpha);

    {
        intermediate.push_back(afterAlpha);
        intermediate.push_back(delta[1]);
        intermediate.push_back(nabla[0]);
        intermediate.push_back(beforeBeta);
        intermediate.push_back(deltaOut[0]);
        intermediate.push_back(tmp1);
    }

    BVRor(model, afterAlpha, delta[0], alpha);
    onlyLargeSwitch_EBCT_enum<branchSize>(model, afterAlpha, delta[1], nabla[0], beforeBeta, deltaOut[0], tmp1, halfNum);
    BVRol(model, afterBeta, beforeBeta, beta);
    BVXor(model, nabla[0], afterBeta, nabla[1]);

    // link deltaOut[1] to delta[1]
    auto tmp2 = NewBoolVec(model, branchSize);
    BVRol(model, tmp2, delta[1], beta);
    BVXor(model, deltaOut[0], tmp2, deltaOut[1]);

    // link nablaIn[1] to nabla[1]
    auto tmp3 = NewBoolVec(model, branchSize);
    BVRol(model, tmp3, nablaIn[1], beta);
    BVXor(model, nabla[0], tmp3, nabla[1]);
    return;
}

template<int branchSize>
static void addSwitchM(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, const int mNum, const int halfNum)
{
    std::vector< std::array<BoolVec, 2> > EBCTs;

    std::array<BoolVec, 2> initEBCTd = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
    std::array<BoolVec, 2> initEBCTn = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };

    EBCTs.push_back(initEBCTd);
    EBCTs.push_back(initEBCTn);
    _addSwitchUBCT<branchSize>(model, delta, initEBCTn, initEBCTd, halfNum);

    for (int i = 0; i < mNum; ++i) {
        std::array<BoolVec, 2> EBCTd = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
        std::array<BoolVec, 2> EBCTn = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
        EBCTs.push_back(EBCTd);
        EBCTs.push_back(EBCTn);
        _addSwitchEBCT<branchSize>(model, EBCTs[2 * i], EBCTn, EBCTd, EBCTs[2 * i + 1], halfNum);
    }

    _addSwitchLBCT<branchSize>(model, EBCTs[2 * mNum], nabla, EBCTs[2 * mNum + 1], halfNum);
    return;
}

template<int branchSize>
void search(const int preRound, const int postRound, const int mNum, const int halfNum)
{
    constexpr int blockSize = 2 * branchSize;

    SatParameters parameters;
    //parameters.set_search_branching(SatParameters::FIXED_SEARCH);
    parameters.set_num_search_workers(10);
    parameters.set_log_search_progress(true);

    CpModelBuilder cp_model;
    std::vector<IntVar> probs;
    std::vector< std::array<BoolVec, 2> > allState;

    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(inputDiff);

    std::vector<BoolVar> inputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            inputBits.push_back(inputDiff[i][j]);
    cp_model.AddBoolOr(inputBits);

    for (int i = 1; i <= preRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 10));

        if (i == 1) {
            //cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1)));
        }
        if (i != 1 && i != preRound ) {
            //cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1) * 3));
            //cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 5));
        }
    }

    auto e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
    cp_model.AddEquality(e1Prob, LinearExpr::Sum(probs));

    std::array<BoolVec, 2> switchState = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(switchState);

    //addSwitch2(cp_model, allState[preRound], switchState, halfNum, halfNum);
    addSwitchM<branchSize>(cp_model, allState[preRound], switchState, mNum, halfNum);

    for (int i = 1; i <= postRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[preRound + 1 + i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 10));

        if (i == 3) {
            //cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1)));
        }
        if (i != 1 && i != postRound) {
            //cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1) * 3));
            //cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 5));
        }
    }

    if (false) {
    //const std::array<unsigned long long int, 2> inputV{{ 0x92400040, 0x40104200 }};
    //const std::array<unsigned long long int, 2> outputV{{ 0x84008020, 0x80008124 }};
    const std::array<unsigned long long int, 2> inputV {{ 0b0010100000000000, 0b0000000000010000 }};
    const std::array<unsigned long long int, 2> outputV{{ 0b1000000000000000, 0b1000010000001010 }};

    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j) {
            auto tmpc = ((inputV[i] >> j) & 1) == 0 ? cp_model.FalseVar() : cp_model.TrueVar();
            cp_model.AddEquality(allState[0][i][j], tmpc);
        }

    for (int i = 1; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j) {
            auto tmpc = ((outputV[i] >> j) & 1) == 0 ? cp_model.FalseVar() : cp_model.TrueVar();
            cp_model.AddEquality(allState[preRound + 1 + postRound][i][j], tmpc);
        }

    }

    std::vector<BoolVar> outputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            outputBits.push_back(allState[preRound + 1 + postRound][i][j]);
    cp_model.AddBoolOr(outputBits);

    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    cp_model.AddEquality(totalProb, LinearExpr::Sum(probs));

    cp_model.Maximize(totalProb);

    auto model_built = cp_model.Build();

    //const auto response = Solve(model_built);
    const auto response = SolveWithParameters(model_built, parameters);
    const auto status = response.status();

    // CpSolverStatus::INFEASIBLE = 3
    if (status == CpSolverStatus::OPTIMAL || status == CpSolverStatus::FEASIBLE) {
        cout << "==== pre-rounds: " << preRound << ", post-rounds: " << postRound << ", m-rounds: " << mNum + 2 << " ====" << endl << endl;
        std::vector<int> tmp;

        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j)
                tmp.push_back(SolutionIntegerValue(response, inputDiff[i][j]));
        }
        cout << "inputDiff: " << endl;
        printm<branchSize>(tmp);

        tmp.clear();
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j)
                tmp.push_back(SolutionIntegerValue(response, allState[preRound][i][j]));
        }
        cout << "E1 output diff: " << endl;
        printm<branchSize>(tmp);

        tmp.clear();
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j)
                tmp.push_back(SolutionIntegerValue(response, allState[preRound + 1][i][j]));
        }
        cout << "E2 input diff: " << endl;
        printm<branchSize>(tmp);

        tmp.clear();
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j)
                tmp.push_back(SolutionIntegerValue(response, allState[preRound + 1 + postRound][i][j]));
        }
        cout << "outputDiff: " << endl;
        printm<branchSize>(tmp);

        unsigned long long int dnlrv[6];
        cout << "UBCT: " << endl;
        for (int i = 0; i < 5; ++i) {
            cout << "0b";
            dnlrv[i] = 0;
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(response, intermediate[i][branchSize - 1 - j]);
                cout << bit;
                dnlrv[i] = (dnlrv[i] << 1) + (bit&1);
            }
            cout << endl;
        }
        if (branchSize < 64 / 2) {
            const auto ubct_entryv = ubct_entry(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], branchSize);
            cout << ubct_entryv << " = 2^{" << log2(ubct_entryv) << "}" << endl;
        } else {
            const auto ubct_prob = ubct_entry128(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], branchSize);
            cout << ubct_prob << " = 2^{" << log2(ubct_prob) << "}" << endl;
        }

        cout << endl << "EBCT: " << endl;
        for (int mi = 0; mi < mNum; ++mi) {
            for (int i = 0; i < 6; ++i) {
                dnlrv[i] = 0;
                //cout << "0b";
                for (int j = 0; j < branchSize; ++j) {
                    const unsigned int bit = SolutionIntegerValue(response, intermediate[5 + 6 * mi + i][branchSize - 1 - j]);
                    //cout << bit;
                    dnlrv[i] = (dnlrv[i] << 1) + (bit&1);
                }
                //cout << " | ";
            }
            if (branchSize < 64 / 2) {
                const auto ebct_entryv = ebct_entry(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], dnlrv[5], branchSize);
                cout << ebct_entryv << " = 2^{" << log2(ebct_entryv) << "}" << endl;
            } else {
                const auto ebct_prob = ebct_entry128(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], dnlrv[5], branchSize);
                cout << ebct_prob << " = 2^{" << log2(ebct_prob) << "}" << endl;
            }
        }

        cout << endl << "LBCT: " << endl;
        for (int i = 0; i < 5; ++i) {
            cout << "0b";
            dnlrv[i] = 0;
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(response, intermediate[5 + 6 * mNum + i][branchSize - 1 - j]);
                cout << bit;
                dnlrv[i] = (dnlrv[i] << 1) + (bit&1);
            }
            cout << endl;
        }
        if (branchSize < 64 / 2) {
            const unsigned long long lbct_entryv = lbct_entry(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], branchSize);
            cout << lbct_entryv << " = 2^{" << log2(lbct_entryv) << "}" << endl;
        } else {
            const auto lbct_prob = lbct_entry128(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], branchSize);
            cout << lbct_prob << " = 2^{" << log2(lbct_prob) << "}" << endl;
        }

        cout << "probs:" << endl;
        for (auto &prob : probs) {
            cout << (branchSize - 1) - SolutionIntegerValue(response, prob) << endl;
        }
        cout << endl;

        cout << "isHalf: " << endl;
        for (auto &bit : interBits) {
            cout << SolutionIntegerValue(response, bit) << endl;
        }
        cout << endl;

        cout << "intermediate: " << endl;
        const int _tmpsize = intermediate.size();
        for (int i = 14; i < _tmpsize; ++i) {
            cout << "0b";
            for (int j = 0; j < branchSize; ++j)
                cout << SolutionIntegerValue(response, intermediate[i][branchSize - 1 - j]);
            cout << endl;
        }

        auto prob = SolutionIntegerValue(response, totalProb);
        auto prob1 = SolutionIntegerValue(response, e1Prob);
        //auto sprob = SolutionIntegerValue(response, switchProb);
        //cout << "switchProb: " << prob << " / 2^" << blockSize << endl;
        cout << "e1Prob: 2^{" << prob1 << "} / 2^" << (preRound * (branchSize - 1))
             << " = 2^{-" << preRound * (branchSize - 1) - prob1 << "}" << endl;
        cout << "totalProb: (2^{" << prob << "} / 2^" << (branchSize - 1) * (preRound + postRound)  << ")^2"
             << " = (2^{-" << (branchSize - 1) * (preRound + postRound) - prob << "}) ^ 2"
             << " = 2^{-" << (branchSize - 1) * (preRound + postRound) * 2 - prob * 2 << "}" << endl;
        cout << "wall time: " << response.wall_time() << endl;
    }

    return;
}

template<int branchSize>
static int searchT(const int preRound, const int postRound, const int mNum, const int halfNum, const int first0, const int second0)
{
    constexpr int blockSize = 2 * branchSize;

    SatParameters parameters;
    //parameters.set_search_branching(SatParameters::FIXED_SEARCH);
    parameters.set_num_search_workers(12);
    parameters.set_log_search_progress(true);

    CpModelBuilder cp_model;
    std::vector<IntVar> probs;
    std::vector< std::array<BoolVec, 2> > allState;

    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(inputDiff);

    std::vector<BoolVar> inputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            inputBits.push_back(inputDiff[i][j]);
    cp_model.AddBoolOr(inputBits);

    for (int i = 1; i <= preRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 15));

        if (i == first0) {
            cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1)));
        }
        if (i == 3 || i == 4 || i == 5) {
            //cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1) * 3));
            //cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 2));
        }
    }

    auto e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
    cp_model.AddEquality(e1Prob, LinearExpr::Sum(probs));

    std::array<BoolVec, 2> switchState = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(switchState);

    //addSwitch2(cp_model, allState[preRound], switchState, halfNum, halfNum);
    addSwitchM<branchSize>(cp_model, allState[preRound], switchState, mNum, halfNum);

    for (int i = 1; i <= postRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[preRound + 1 + i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 15));

        if (i == second0) {
            cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1)));
        }
        if (i == 4 || i == 5 || i == 6) {
            //cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1) * 3));
            //cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 2));
        }
    }

    std::vector<BoolVar> outputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            outputBits.push_back(allState[preRound + 1 + postRound][i][j]);
    cp_model.AddBoolOr(outputBits);

    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    cp_model.AddEquality(totalProb, LinearExpr::Sum(probs));

    cp_model.Maximize(totalProb);

    auto model_built = cp_model.Build();

    //const auto response = Solve(model_built);
    const auto response = SolveWithParameters(model_built, parameters);
    const auto status = response.status();

    // CpSolverStatus::INFEASIBLE = 3
    if (status == CpSolverStatus::OPTIMAL || status == CpSolverStatus::FEASIBLE) {
        cout << "==== pre-rounds: " << preRound << ", post-rounds: " << postRound << ", m-rounds: " << mNum + 2 << " ====" << endl << endl;
        std::vector<int> tmp;

        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j)
                tmp.push_back(SolutionIntegerValue(response, inputDiff[i][j]));
        }
        cout << "inputDiff: " << endl;
        printm<branchSize>(tmp);

        tmp.clear();
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j)
                tmp.push_back(SolutionIntegerValue(response, allState[preRound][i][j]));
        }
        cout << "E1 output diff: " << endl;
        printm<branchSize>(tmp);

        tmp.clear();
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j)
                tmp.push_back(SolutionIntegerValue(response, allState[preRound + 1][i][j]));
        }
        cout << "E2 input diff: " << endl;
        printm<branchSize>(tmp);

        tmp.clear();
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j)
                tmp.push_back(SolutionIntegerValue(response, allState[preRound + 1 + postRound][i][j]));
        }
        cout << "outputDiff: " << endl;
        printm<branchSize>(tmp);

        unsigned long long int dnlrv[6];
        cout << "UBCT: " << endl;
        for (int i = 0; i < 5; ++i) {
            cout << "0b";
            dnlrv[i] = 0;
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(response, intermediate[i][branchSize - 1 - j]);
                cout << bit;
                dnlrv[i] = (dnlrv[i] << 1) + (bit&1);
            }
            cout << endl;
        }
        if (branchSize < 64 / 2) {
            const auto ubct_entryv = ubct_entry(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], branchSize);
            cout << ubct_entryv << " = 2^{" << log2(ubct_entryv) << "}" << endl;
        } else {
            const auto ubct_prob = ubct_entry128(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], branchSize);
            cout << ubct_prob << " = 2^{" << log2(ubct_prob) << "}" << endl;
        }

        cout << endl << "EBCT: " << endl;
        for (int mi = 0; mi < mNum; ++mi) {
            for (int i = 0; i < 6; ++i) {
                dnlrv[i] = 0;
                //cout << "0b";
                for (int j = 0; j < branchSize; ++j) {
                    const unsigned int bit = SolutionIntegerValue(response, intermediate[5 + 6 * mi + i][branchSize - 1 - j]);
                    //cout << bit;
                    dnlrv[i] = (dnlrv[i] << 1) + (bit&1);
                }
                //cout << " | ";
            }
            if (branchSize < 64 / 2) {
                const auto ebct_entryv = ebct_entry(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], dnlrv[5], branchSize);
                cout << ebct_entryv << " = 2^{" << log2(ebct_entryv) << "}" << endl;
            } else {
                const auto ebct_prob = ebct_entry128(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], dnlrv[5], branchSize);
                cout << ebct_prob << " = 2^{" << log2(ebct_prob) << "}" << endl;
            }
        }

        cout << endl << "LBCT: " << endl;
        for (int i = 0; i < 5; ++i) {
            cout << "0b";
            dnlrv[i] = 0;
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(response, intermediate[5 + 6 * mNum + i][branchSize - 1 - j]);
                cout << bit;
                dnlrv[i] = (dnlrv[i] << 1) + (bit&1);
            }
            cout << endl;
        }
        if (branchSize < 64 / 2) {
            const unsigned long long lbct_entryv = lbct_entry(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], branchSize);
            cout << lbct_entryv << " = 2^{" << log2(lbct_entryv) << "}" << endl;
        } else {
            const auto lbct_prob = lbct_entry128(dnlrv[0], dnlrv[1], dnlrv[2], dnlrv[3], dnlrv[4], branchSize);
            cout << lbct_prob << " = 2^{" << log2(lbct_prob) << "}" << endl;
        }

        cout << "probs:" << endl;
        for (auto &prob : probs) {
            cout << (branchSize - 1) - SolutionIntegerValue(response, prob) << endl;
        }
        cout << endl;

        cout << "isHalf: " << endl;
        for (auto &bit : interBits) {
            cout << SolutionIntegerValue(response, bit) << endl;
        }
        cout << endl;

        cout << "intermediate: " << endl;
        const int _tmpsize = intermediate.size();
        for (int i = 14; i < _tmpsize; ++i) {
            cout << "0b";
            for (int j = 0; j < branchSize; ++j)
                cout << SolutionIntegerValue(response, intermediate[i][branchSize - 1 - j]);
            cout << endl;
        }

        const auto prob = SolutionIntegerValue(response, totalProb);
        const auto prob1 = SolutionIntegerValue(response, e1Prob);
        //auto sprob = SolutionIntegerValue(response, switchProb);
        //cout << "switchProb: " << prob << " / 2^" << blockSize << endl;
        cout << "e1Prob: 2^{" << prob1 << "} / 2^" << (preRound * (branchSize - 1))
             << " = 2^{-" << preRound * (branchSize - 1) - prob1 << "}" << endl;
        cout << "totalProb: (2^{" << prob << "} / 2^" << (branchSize - 1) * (preRound + postRound)  << ")^2"
             << " = (2^{-" << (branchSize - 1) * (preRound + postRound) - prob << "}) ^ 2"
             << " = 2^{-" << (branchSize - 1) * (preRound + postRound) * 2 - prob * 2 << "}" << endl;
        cout << "wall time: " << response.wall_time() << endl;

        return (branchSize - 1) * (preRound + postRound) - prob;
    }

    return 200;
}


int main()
{
    search<32 / 2>(4, 4, 0, 16);
    return 0;
}
