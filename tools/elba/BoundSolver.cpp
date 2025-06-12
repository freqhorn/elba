#include "deep/BoundSolverV2.hpp"

using namespace ufo;
using namespace std;

static inline bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return atoi(argv[i+1]);
    }
  }
  return defValue;
}

string getStrValue(const char * opt, string defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return string(argv[i+1]);
    }
  }
  return defValue;
}

vector<string> getCommaSepStrValues(const char * opt, vector<string> defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      stringstream tmpss(argv[i+1]);
      vector<string> values;
      while (tmpss.good()) {
        string tmpstr;
        getline(tmpss, tmpstr, ',');
        values.push_back(tmpstr);
      }
      return values;
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, argc, argv) || getBoolValue("-h", false, argc, argv) || argc == 1)
  {
    outs() << "Usage: ./elba [options]\n\n"
              "Options:\n"
              "  -h, --help       Display this help message\n"
              "  --learn <int>    Set the learning parameter (default: 2)\n"
              "  --limit <int>    Set the unrolling limit (default: 3)\n"
              "  --debug <int>    Set the debug level (default: 0)\n"
              "  --md <int>       Set the mutation depth for data results (default: 0)\n"
              "  --data-guards    Disable the use of data guards (default: enabled)\n"
              "  --gj             Enable Gauss Jordan elimination\n"
              "  --dc             Enable Connect algorithm (Default if neither GJ or Connect chosen.)\n"
              "  --ac             Enable abstraction of large constants\n"
              "  --di             Enable data inference\n"
              "  --mi             Enable mutation of inferred results\n";
    return 0;
  }

  int learn = getIntValue("--learn", 2, argc, argv); 
  int limit = getIntValue("--limit", 3, argc, argv); // unrolling limit
  int cex = getIntValue("--cex", 0, argc, argv);
  int str = getIntValue("--stren", 5, argc, argv);
  int debug = getIntValue("--debug", 0, argc, argv);
  bool useDataGrds = !getBoolValue("--data-guards", false, argc, argv); // use data guards
  bool gj = getBoolValue("--gj", false, argc, argv);  // do Gauss Jordan
  bool dc = getBoolValue("--dc", false, argc, argv);  // do connect
  bool ac = getBoolValue("--ac", false, argc, argv);  // abstract large constants
  bool iwd = getBoolValue("--di", false, argc, argv); // data inference
  bool imp = getBoolValue("--ei", false, argc, argv); // enable second implication
  bool mi = getBoolValue("--mi", false, argc, argv);  // mutate inferred
  bool so = getBoolValue("--so", false, argc, argv);  // separate ops.
  int  md = getIntValue("--md", 0, argc, argv);       // mutate results from data.
  bool tk = false;
  bool data2 = getBoolValue("--data2", false, argc, argv);
  bool doPhases = getBoolValue("--phase-data", false, argc, argv);

  std::ifstream infile(argv[argc-1]);
  if (!infile.good())
  {
    outs() << "Could not read file \"" << argv[argc-1] << "\"\n";
    return 0;
  }

  if(!dc && !gj) dc = true;

  if(learn == 1) 
    learnBounds(string(argv[argc-1]), cex, str, useDataGrds, data2, doPhases, debug);
  else
    learnBoundsV2(string(argv[argc-1]), cex, str, useDataGrds, data2, doPhases, limit,
                  gj, dc, ac, iwd, imp, mi, so, tk, md, debug);
    
  return 0;
}
