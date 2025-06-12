#ifndef DATALEARNERTOO__HPP__
#define DATALEARNERTOO__HPP__

#include <cmath>
#include <vector>
#include <algorithm>

#include "Horn.hpp"
#include "BndExpl.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;
using namespace boost::multiprecision;

typedef boost::multiprecision::cpp_int CPPINT;
typedef boost::multiprecision::cpp_rational RATIONAL;
typedef vector<vector<RATIONAL>> matrix;

namespace ufo
{
  class basisFinder
  {
  private:
    int numVars;
    int numRows;
    matrix A;
    vector<bool> freeVars;
    int debug;

    RATIONAL rmod(RATIONAL x, RATIONAL y)
    { // Modulus for rationals
      RATIONAL res;
      res = x / y;

      while (res >= 1)
      {
        res -= 1;
      }
      return res;
    }

    RATIONAL gcd(RATIONAL x, RATIONAL y)
    { // GCD for rationals
      RATIONAL g = boost::multiprecision::gcd(numerator(x), numerator(y));
      RATIONAL l = boost::multiprecision::lcm(denominator(x), denominator(y));
      RATIONAL res = g / l;
      return res;
    }

    RATIONAL gcd(vector<RATIONAL> v)
    { // GCD for a vector of rationals
      RATIONAL res = 0;
      if (!v.empty())
      {
        res = v[0];
        for (int i = 1; i < v.size(); i++)
        {
          res = gcd(v[i], res);
          if (res == 1)
            return res;
        }
      }
      return res;
    }

    cpp_int lcm(vector<cpp_int> v)
    {
      cpp_int res = 1;

      if (!v.empty())
      {
        res = v[0];
        for (int i = 1; i < v.size(); i++)
        {
          res = boost::multiprecision::lcm(res, v[i]);
        }
      }
      return res;
    }

    int pivotIndex(matrix &A, int r)
    {
      for (int j = 0; j < numVars; j++)
      {
        if (A[r][j] != 0)
          return j;
      }
      return -1;
    }

    int rowToSwap(matrix &A, const int p)
    {
      int pivotRow = p;

      for (int i = p; i < numRows; i++)
      {
        if (A[i][p] != 0)
        {
          pivotRow = i;
          break;
        }
      }

      return pivotRow;
    }

    void reducedRowEchelonForm(matrix &A)
    {
      unsigned int cur_row = 0;
      unsigned int cur_col = 0;

      while (cur_row < numRows && cur_col < numVars)
      {
        if (A[cur_row][cur_col] == 0)
        {
          int r = rowToSwap(A, cur_col);
          if (r == cur_col)
          {
            cur_col++;
            continue;
          }
          std::swap(A[r], A[cur_row]);
        }

        // reduce pivot to 1
        if (A[cur_row][cur_col] != 1)
        {
          RATIONAL divisor = A[cur_row][cur_col];
          if (divisor == 0)
            continue;
          for (int i = cur_col; i < numVars; i++)
          {
            A[cur_row][i] /= divisor;
          }
        }
        // Now reduce rows below
        for (int i = cur_row + 1; i < numRows; i++)
        {
          RATIONAL divisor = A[i][cur_col];
          if (divisor == 0)
            continue;
          for (int j = cur_col; j < numVars; j++)
          {
            A[i][j] /= divisor;
            A[i][j] = A[cur_row][j] - A[i][j] * A[cur_row][cur_col];
          }
          A[i][cur_col] = 0;
        }
        cur_row++;
        cur_col++;
      }

      // reduce above
      while (cur_row > 1)
      {
        cur_row--;
        int cur_col = pivotIndex(A, cur_row);
        if (cur_col < 0)
          continue;

        for (int i = cur_row - 1; i >= 0; i--)
        {
          RATIONAL divisor = A[i][cur_col];
          if (divisor == 0)
            continue;
          for (int j = numVars - 1; j >= cur_col; j--)
          {
            A[i][j] = A[i][j] - A[cur_row][j] * divisor;
          }
        }
      }
    }

    void initFreeVars()
    {
      for (int i = 0; i < numVars; i++)
      {
        freeVars.push_back(true);
      }
    }

    void determineFreeVars(matrix &A)
    {
      initFreeVars();
      for (int i = 0; i < numRows; i++)
      {
        int pivot = pivotIndex(A, i);
        if (pivot >= 0)
        {
          freeVars[pivot] = false;
        }
      }
    }

    void printFreeVars()
    {
      bool pr = false;
      cout << "==  FREE VARS  ==\n";
      for (int i = 0; i < freeVars.size(); i++)
      {
        if (freeVars[i])
        {
          if (pr)
            cout << ", ";
          cout << "x" << i;
          pr = true;
        }
      }
      if (pr)
        cout << "\n\n";
    }

    void printVector(vector<RATIONAL> bv)
    {
      cout << "==  VECTOR  ==\n";
      for (auto v : bv)
      {
        cout << v << "\n";
      }
      cout << "\n";
    }

    matrix kernelBasis(matrix &A)
    {
      matrix basis;
      vector<RATIONAL> basisVector;

      for (int b = 0; b < freeVars.size(); b++)
      {
        if (!freeVars[b])
          continue;
        for (int i = 0; i < numVars; i++)
        {
          if (b == i)
          {
            basisVector.push_back(1);
          }
          else
          {
            basisVector.push_back(0);
          }
        } // fill in zeros for all vector vars.
        // Change var values that are not zero. Namely values from pivot rows and a 1 for the var itself.
        for (int i = 0; i < numRows; i++)
        {
          int pivot = pivotIndex(A, i);
          if (pivot >= 0 && basisVector[pivot] == 0)
          {
            RATIONAL val = A[i][b];
            if (val == 0)
              basisVector[pivot] = val;
            else
              basisVector[pivot] = -val;
          }
          else
          {
            break;
          }
        }
        basis.push_back(basisVector);
        if (debug >= 1)
          printVector(basisVector);
        basisVector.clear();
      }
      return basis;
    }

    matrix findBasis(matrix &A)
    {
      // identify free vars and extract basis vectors
      determineFreeVars(A);
      if (debug >= 1)
      {
        printFreeVars();
        cout << "\n";
      }
      matrix basis = kernelBasis(A);
      return basis;
    }

    void printCands(matrix &B)
    {
      int n = B.size();
      int m;
      if (n == 0)
      {
        m = 0;
      }
      else
      {
        m = B[0].size();
      }

      cout << "==  CANDS  ==\n";
      for (int i = 0; i < n; i++)
      {
        for (int j = 0; j < m; j++)
        {
          cout << B[i][j] << "* x" << j << " + ";
        }
        cout << " = 0\n";
      }
    }

    void removeFractions(matrix &A)
    {
      for (int i = 0; i < A.size(); i++)
      {
        vector<cpp_int> denominators;
        for (int j = 0; j < A[i].size(); j++)
        {
          cpp_int d = denominator(A[i][j]);
          denominators.push_back(d);
        }
        cpp_int multiplier = lcm(denominators);
        for (int j = 0; j < numVars; j++)
        {
          A[i][j] = A[i][j] * multiplier;
        }
      }
      if (debug >= 1)
      {
        printMatrix(A);
        cout << "\n";
      }
    }

  public:
    basisFinder(matrix &_A, int dbg = 0) : A(_A), debug(dbg)
    {
      if (A.empty())
      {
        numVars = 0;
        numRows = 0;
        return;
      }

      numVars = A[0].size();
      numRows = A.size();
    }

    void printMatrix(matrix &A)
    {
      outs() << "==  MATRIX  ==\n";
      int n = A.size();
      int m = A[0].size();
      for (int i = 0; i < n; i++)
      {
        outs() << "  ";
        for (int j = 0; j < m; j++)
        {
          if (j > 0)
            cout << " ";
          cout << A[i][j];
        }
        cout << "\n";
      }
      //  cout << "\n";
    }

    matrix findKernelBasis()
    {
      numVars = A[0].size();
      numRows = A.size();

      if (debug >= 1)
      {
        printMatrix(A);
        cout << "\n";
      }

      reducedRowEchelonForm(A);

      if (debug >= 1)
      {
        printMatrix(A);
        cout << "\n";
      }

      // Now find basis vectors.
      matrix basis = findBasis(A);
      if (!basis.empty())
        removeFractions(basis);
      if (debug >= 1)
      {
        printCands(basis);
      }

      return basis;
    }
  }; // End class basisFinder

  class DataLearner2
  {
  private:
    CHCs &ruleManager;
    BndExpl bnd;
    ExprFactory &m_efac;
    map<Expr, matrix> basis;
    map<Expr, vector<vector<double>>> models;
    map<Expr, ExprVector> invVars;
    map<Expr, ExprSet> dataCands;
    vector<RATIONAL> firstRow;
    int debug;

    void connectCands(Expr srcRel)
    {
      // dataCands.clear();
      if(debug >= 3) 
      {
        matrix A = doubleToRational(models[srcRel]);
        basisFinder bf(A, debug);
        bf.printMatrix(A);
      }

      if (models[srcRel].size() < 2)
      {
        return;
      }

      auto ritr = models[srcRel].rbegin();
      vector<double> e1 = *ritr;
      ritr++;
      vector<double> e2 = *ritr;
      ExprVector ev;

      int n = invVars[srcRel].size();
      
      for (int i = 0; i < n; i++)
      {
        for (int j = i + 1; j < n; j++)
        {
          Expr r1, r2, l1, l2, l, r;
          r1 = mkMPZ(cpp_int(e2[j] - e1[j]), m_efac);
          // outs() << "r1: " << r1 << "\n";
          r2 = mk<MINUS>(invVars[srcRel][i], mkMPZ(cpp_int(e1[i]), m_efac));
          l1 = mkMPZ(cpp_int(e2[i] - e1[i]), m_efac);
          l2 = mk<MINUS>(invVars[srcRel][j], mkMPZ(cpp_int(e1[j]), m_efac));
          if (e2[j] - e1[j] == 0)
          {
            r1 = mkMPZ(0, m_efac);
          }
          else
          {
            r1 = mk<MULT>(r1, r2);
          }
          if (e2[i] - e1[i] == 0)
          {
            l1 = mkMPZ(0, m_efac);
          }
          else
          {
            l1 = mk<MULT>(l1, l2);
          }
          l = mk<EQ>(r1, l1);
          ev.push_back(l);
          if (debug >= 1)
            outs() << "  CONNECT: " << *ev.back() << "\n";
        }
      }
      if (debug >= 1)
        outs() << "\n";
      // ADD or SUBTRACT each equation from another to generate data candidates.
      for (int i = 0; i < ev.size(); i++)
      {
        dataCands[srcRel].insert(normalize(ev[i]));
        for (int j = i + 1; j < ev.size(); j++)
        {
          Expr r = mk<MINUS>(ev[i]->right(), ev[j]->right());
          Expr l = mk<MINUS>(ev[i]->left(), ev[j]->left());
          l = mk<EQ>(l, r);
          l = normalize(l);
          dataCands[srcRel].insert(l);
          if (debug >= 1)
            outs() << "  CONNECT(-): " << l << "\n";

          r = mk<PLUS>(ev[i]->right(), ev[j]->right());
          l = mk<PLUS>(ev[i]->left(), ev[j]->left());
          l = mk<EQ>(l, r);
          l = normalize(l);
          dataCands[srcRel].insert(l);
          if (debug >= 1)
            outs() << "  CONNECT(+): " << l << "\n";
        }
      }
    }

    Expr dotProduct(Expr srcRel, vector<RATIONAL> row, bool addToDataCands = true)
    {
      ExprVector terms;
      ExprSet cands;
      int n = 0;
      for (int i = 0; i < invVars[srcRel].size(); i++)
      {
        terms.clear();
        terms.push_back(invVars[srcRel][i]);
        terms.push_back(mkMPZ(-numerator(row[i+1]), srcRel->getFactory()));
        cands.insert(simplifyArithm(mk<EQ>(mkplus(terms, srcRel->getFactory()), mkMPZ(0, srcRel->getFactory()))));
        n++;
      }
      if (debug >= 3)
      {
        outs() << "CANDS FROM dotProduct: " << n << "\n";
        for(auto &c : cands) {
          outs() << "  " << *c << "\n";
        }
      }

      if (addToDataCands) dataCands[srcRel].insert(cands.begin(), cands.end());

      return conjoin(cands, srcRel->getFactory());
    }

    void candsFromBasis(Expr srcRel)
    {
      ExprVector terms;
      ExprSet cands;
      if (basis[srcRel].empty())
      {
        if (debug >= 1)
          outs() << "BASIS was empty\n";
        return;
      }
      int cnt = 0;
      for (auto &v : basis[srcRel])
      {
        terms.clear();
        for (int i = 1; i < v.size(); i++)
        {
          Expr cnst = mkMPZ(numerator(v[i]), srcRel->getFactory());
          Expr term = mk<MULT>(cnst, invVars[srcRel][i - 1]);
          terms.push_back(term);
        }
        cnt++;
        Expr cnst = mkMPZ(-numerator(v[0]), srcRel->getFactory());
        Expr datcand = mk<EQ>(mkplus(terms, srcRel->getFactory()), cnst);
        cands.insert(normalize(datcand));
      }
      if (debug >= 1)
        outs() << "CANDS FROM BASIS: " << cnt << "\n";
      if(debug >= 2) {
        for(auto &c : cands) {
          outs() << "  " << *c << "\n";
        }
      }
      dataCands[srcRel].insert(cands.begin(), cands.end());
    }

    matrix doubleToRational(vector<vector<double>> models)
    {
      matrix A;
      for (int i = 0; i < models.size(); i++)
      {
        vector<RATIONAL> temp;
        temp.push_back(static_cast<RATIONAL>(1));
        for (int j = 0; j < models[0].size(); j++)
        {
          temp.push_back(static_cast<RATIONAL>(models[i][j]));
        }
        A.push_back(temp);
      }
      return A;
    }

    void computeData(Expr srcRel)
    {
      matrix A = doubleToRational(models[srcRel]);

      if (A.empty())
        return;
      basisFinder bf(A, debug);

      firstRow = *A.begin();
      auto row = firstRow;

      if (row.empty())
        return;

      // Now make cands from the reduced matrix.
      basis[srcRel] = bf.findKernelBasis();
      candsFromBasis(srcRel);
    }

  public:
    DataLearner2(CHCs &r, EZ3 &z3, int _debug = 0) : ruleManager(r), bnd(ruleManager, (_debug > 0)), m_efac(r.m_efac), debug(_debug) {}

    boost::tribool connectPhase(Expr src, Expr dst, int k = 1,
                    Expr srcRel = NULL, Expr block = NULL, Expr invs = NULL,
                    Expr preCond = NULL, bool doGJ = false, bool doConnect = false)
      {
        boost::tribool res = bnd.unrollAndExecuteTermPhase
          (src, dst, srcRel, invVars[srcRel], models[srcRel], block, k);

      if (!res)
      {
        if (debug >= 1)
          outs() << "BMC formula unsat\n";
        return res;
      }

      if (models[srcRel].empty()) return false;

      if(doConnect) connectCands(srcRel);
      if(doGJ) computeData(srcRel); // Gauss Jordan Elimination method.

      return res;
    }

    ExprVector exprForRows(Expr srcRel)
    {
      if(models[srcRel].empty()) return ExprVector();

      matrix A = doubleToRational(models[srcRel]);

      ExprVector rowsExpr;
      for(auto &row : A) 
      {
        rowsExpr.push_back(dotProduct(srcRel, row, false));
      }

      return rowsExpr;
    }

    boost::tribool computeData(Expr srcRel, map<Expr, ExprVector> &arrRanges, map<Expr, ExprSet> &constr)
    {
      if (debug >= 1)
        outs() << "\n======== COMPUTE DATA ========\n";
      models.clear();
      boost::tribool res = bnd.unrollAndExecuteMultiple(invVars, models, arrRanges, constr);

      if (!res)
      {
        if (debug >= 1)
          outs() << "BMC formula unsat\n";
        return res;
      }

      computeData(srcRel);

      return res;
    }

    boost::tribool computeDataPhase(Expr srcRel, Expr splitter, Expr invs, bool fwd, ExprSet &constr)
    {
      if (debug >= 1)
        outs() << "\n======== COMPUTE DATA PHASE ========\n";
      models.clear();
      //  Get data matrix.
      boost::tribool res = bnd.unrollAndExecuteSplitter(srcRel, invVars[srcRel], models[srcRel], splitter, invs, fwd, constr);

      if (!res)
      {
        if (debug >= 1)
          outs() << "BMC formula unsat\n";
        return res;
      }

      computeData(srcRel);

      return res;
    }

    void getDataCands(ExprSet& cands, Expr rel) { cands = dataCands[rel]; }

  }; // End class DataLearner2

}

#endif