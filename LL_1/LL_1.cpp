/* ***********************************************************************
   > File Name: LL_1.cpp
   > Author: Key
   > Mail: keyld777@gmail.com
   > Created Time: Fri 21 Apr 2017 02:22:19 PM CST
 ********************************************************************** */
#include <algorithm>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <vector>

#define WAIT_TO_JUDGE 0
#define TO_EMPTY 12345
#define NOT_TO_EMPTY 54321

using namespace std;

struct NT {       //非终结符
    char m_name;  //非终结符
    int is_empty; //能否通过这个非终结符推导出空 （这里用 & 表示空 其中 0 表示不确定，1表示可行，-1表示不可行
    int num;      //产生式中 以该非终结符为左部的 产生式个数
    bool vis;     //访问标记
    set<char> FirstSet;
    set<char> FollowSet;

    NT()
        : is_empty(0)
        , num(0)
        , vis(false){};
    NT(char c)
        : m_name(c)
        , is_empty(0)
        , num(0)
        , vis(false){};
    bool operator==(const NT& cmp) const
    {
        return m_name == cmp.m_name;
    }
};

struct T { //终结符
    char m_name;
    int is_empty;
    bool vis;

    T()
        : is_empty(0)
        , vis(false){};
    T(char c)
        : m_name(c)
        , is_empty(0)
        , vis(false){};
    bool operator==(const T& cmp) const
    {
        return m_name == cmp.m_name;
    }
};

struct formula {  //产生式
    char left;    //产生式左部
    string right; //产生式右部
    int is_empty;
    bool vis;

    set<char> SelectSet; //Select集合
    set<char> FirstSet;  //First集合

    formula()
        : is_empty(0)
        , vis(false)
    {
    }
    bool operator<(const formula& a) const
    {
        return left < a.left;
    }
};

int FormulaNumber;      //产生式数量
vector<NT> NTs;         //非终结符 向量
vector<T> Ts;           //终结符 向量
vector<formula> Fs;     //产生式 向量
formula* AnalysisTable; //产生式Select分析表
map<char, int> NTIdMap; //获取非终结符的下标
map<char, int> TIdMap;  //获取终结符的下标
char Start;             //开始符
FILE* FP;               //输入文件

void readNT() //读入非终结符 集合
{
    string s;
    cin >> s;
    sort(s.begin(), s.end());
    for (unsigned i = 0; i < s.size(); ++i) {
        NTs.push_back(NT(s[i]));
        NTIdMap.insert(make_pair(s[i], NTIdMap.size()));
    }
}

void readT() //读入终结符 集合
{
    string s;
    cin >> s;
    sort(s.begin(), s.end());
    for (unsigned i = 0; i < s.size(); ++i) {
        Ts.push_back(T(s[i]));
        TIdMap.insert(make_pair(s[i], TIdMap.size()));
    }
}

void readFormula() //读入产生式集合
{
    string s;
    char c;
    formula f;
    for (int i = 0; i < FormulaNumber; ++i) {
        cin >> f.left >> c >> c; // 产生式中间不能有空格
        cin >> f.right;
        NTs[NTIdMap[f.left]].num++;
        Fs.push_back(f);
    }
    sort(Fs.begin(), Fs.end());
}

inline bool isNT(char c) //判断字符 c 是否属于非终结符号集合
{
    return find(NTs.begin(), NTs.end(), NT(c)) != NTs.end();
}

inline bool isT(char c) // 判断字符 c 是否属于终结符号集合
{
    return find(Ts.begin(), Ts.end(), T(c)) != Ts.end();
}

void printFormula() //打印产生式
{
    cout << "Formula:" << endl;
    for (unsigned i = 0; i < Fs.size(); ++i)
        cout << Fs[i].left << "->" << Fs[i].right << endl;
    cout << endl;
}

//推空法则
//1.右部为空则为空
//2.右部含有终结符 或者 已判断不能推空的非终结符 则不能推空 (其中如果存在未判定终结符，则无法判断)
//3.否则能推空(即右部全为非终结符并且都能推空)

void judgeNTIsEmpty() //对于每个非终结符 是否推出空
{
    unsigned done = 0;          //对已经判定的非终结符进行计数
    while (done < NTs.size()) { //直到所有非终结符都被判定才退出
        for (unsigned i = 0; i < Fs.size(); ++i) {
            if (Fs[i].vis || NTs[NTIdMap[Fs[i].left]].is_empty != WAIT_TO_JUDGE) { //处理过,或者已经推导出结果 则跳过
                continue;
            }
            if (Fs[i].right == "&") { //直接推出空
                NTs[NTIdMap[Fs[i].left]].is_empty = TO_EMPTY;
                Fs[i].vis = true; //标记处理过
                done++;
            } else {
                bool hasT = false;
                for (unsigned k = 0; k < Fs[i].right.size(); k++)
                    if (isT(Fs[i].right[k])) {                                //推出终结符 T
                        Fs[i].vis = true;                                     //标记处理过
                        if ((--NTs[NTIdMap[Fs[i].left]].num) == 0)            //NTs[i]的待处理 产生式-1
                            NTs[NTIdMap[Fs[i].left]].is_empty = NOT_TO_EMPTY; //所有产生式被删除
                        done++;
                        hasT = true;
                        break;
                    }
                if (!hasT) {               //右部全为非终结符
                    bool hasWTJ = false;   //是否存在未判定的非终结符
                    bool all_empty = true; //是否可以全推空
                    for (unsigned k = 0; k < Fs[i].right.size(); k++) {
                        if (NTs[NTIdMap[Fs[i].right[k]]].is_empty == WAIT_TO_JUDGE) {
                            hasWTJ = true;
                            break;
                        }
                        if (all_empty && NTs[NTIdMap[Fs[i].right[k]]].is_empty == NOT_TO_EMPTY) //如果产生式右部存在已判定非空 字符，则标记为false
                            all_empty = false;
                    }
                    if (hasWTJ) //如果产生式右部存在无法判定的字符，则该产生式无法判断
                        continue;
                    if (all_empty)
                        NTs[NTIdMap[Fs[i].left]].is_empty = TO_EMPTY; //如果产生式右部 所有字符都能推出 空，则表示左部能推出空
                    else
                        NTs[NTIdMap[Fs[i].left]].is_empty = NOT_TO_EMPTY; //否则不能
                    Fs[i].vis = true;
                    done++;
                }
            }
        }
        cout << "NT Empty:" << endl;
        for (unsigned i = 0; i < NTs.size(); i++)
            cout << NTs[i].m_name << "\t " << (NTs[i].is_empty == TO_EMPTY ? "Empty" : "Not Empty") << endl;
        cout << endl;
    }
}

void judgeFormulaIsEmpty() //产生式是否可推空
{
    bool flag;
    for (unsigned i = 0; i < Fs.size(); i++) {
        if (Fs[i].right[0] == '&') { //输入中不会有 &abc 的形式，如果第一个为 空，则产生式右部为空
            Fs[i].is_empty = TO_EMPTY;
            continue;
        }
        flag = true;
        for (unsigned j = 0; j < Fs[i].right.size(); j++) {
            if (isT(Fs[i].right[j]) || NTs[NTIdMap[Fs[i].right[j]]].is_empty == NOT_TO_EMPTY) { //如果存在终结符 或者 存在已判定不可推空的非终结符
                flag = false;
                break;
            }
        }
        if (flag)
            Fs[i].is_empty = TO_EMPTY;
        else
            Fs[i].is_empty = NOT_TO_EMPTY;
    }
    cout << "Formula Empty:" << endl;
    for (unsigned i = 0; i < Fs.size(); ++i)
        cout << Fs[i].left << "->" << Fs[i].right << "\t " << (Fs[i].is_empty == TO_EMPTY ? "Empty" : "Not Empty") << endl;
    cout << endl;
}

string getFirst(char NTchar) //获取终结符 NTchar 当前的first集合内容
{
    set<char>::iterator it, itend;
    string r;
    it = NTs[NTIdMap[NTchar]].FirstSet.begin();
    itend = NTs[NTIdMap[NTchar]].FirstSet.end();
    while (it != itend) {
        r += *it;
        it++;
    }
    return r;
}

void printFirstSet() // 打印 First 集合
{
    cout << "FirstSet:" << endl;
    for (unsigned i = 0; i < NTs.size(); ++i) {
        cout << NTs[i].m_name << "\t: ";
        if (NTs[i].is_empty == TO_EMPTY)
            cout << '&';
        cout << getFirst(NTs[i].m_name) << endl;
    }
    cout << endl;
}

//First集合计算法则
//0.令右部为right数组 这里的() 为切片操作
//1.right[0]为终结符  则right[0]加入集合
//2.right(0,idx-1)均可推空,right[idx] 则将right(0,idx)集合的并集加入  (这里若first集合未求，对结果并无影响)

void getFirstSet() //获取 First 集合
{
    for (unsigned i = 0; i < Fs.size(); i++) //vis数组初始化
        Fs[i].vis = false;
    while (true) {
        bool hasUpdate = false;                    //更新标记
        for (unsigned i = 0; i < Fs.size(); i++) { //遍历每个 产生式
            if (Fs[i].vis)                         //已访问
                continue;
            if (Fs[i].right[0] == '&') { //如果表达式右部为空
                Fs[i].vis = true;
                continue;
            }
            if (isT(Fs[i].right[0])) { //如果表达式右边第一个是 终结符
                Fs[i].vis = true;
                NTs[NTIdMap[Fs[i].left]].FirstSet.insert(Fs[i].right[0]);
                hasUpdate = false;
                continue;
            }
            for (unsigned k = 0; k < Fs[i].right.size(); k++) {
                if (isT(Fs[i].right[k])) { //如果是终结符 结束右侧查找
                    if (NTs[NTIdMap[Fs[i].left]].FirstSet.insert(Fs[i].right[k]).second)
                        hasUpdate = true;
                    break;
                }
                //如果是非终结符，获取此非终结符的 first
                string r = getFirst(Fs[i].right[k]); //可为空，代表未求
                for (unsigned j = 0; j < r.size(); j++) {
                    if (NTs[NTIdMap[Fs[i].left]].FirstSet.insert(r[j]).second)
                        hasUpdate = true;
                }
                if (NTs[NTIdMap[Fs[i].right[k]]].is_empty == NOT_TO_EMPTY) //如果此非终结符 不能推出空 则结束右侧的查找
                    break;
            }
        }
        if (!hasUpdate) //集合未更新 退出
            break;
    }
    printFirstSet();
}

bool unionSet(set<char>& a, set<char>& b) //集合合并
{
    bool hasUpdate = false;
    set<char>::iterator it = b.begin();
    while (it != b.end()) {
        if (a.insert(*it).second)
            hasUpdate = true;
        ++it;
    }
    return hasUpdate;
}

void getFormulaFirstSet() //获取产生式的First集合
{
    for (unsigned i = 0; i < Fs.size(); ++i) { //遍历所有产生式
        if (Fs[i].right[0] == '&')             //跳过空
            continue;
        for (unsigned j = 0; j < Fs[i].right.size(); ++j) { //遍历产生式右边
            if (isT(Fs[i].right[j])) {                      //如果是终结符，加入first 结束
                Fs[i].FirstSet.insert(Fs[i].right[j]);
                break;
            } else
                unionSet(Fs[i].FirstSet, NTs[NTIdMap[Fs[i].right[j]]].FirstSet);
            if (NTs[NTIdMap[Fs[i].right[j]]].is_empty == NOT_TO_EMPTY) //不能推出空 结束
                break;
        }
    }

    cout << "Formula FirstSet:" << endl;
    for (unsigned i = 0; i < Fs.size(); ++i) {
        set<char>::iterator it = Fs[i].FirstSet.begin();
        cout << Fs[i].left << "->" << Fs[i].right << " \t: ";
        if (Fs[i].is_empty == TO_EMPTY)
            cout << '&';
        while (it != Fs[i].FirstSet.end()) {
            cout << *it;
            ++it;
        }
        cout << endl;
    }
    cout<<endl;
}

void printFollowSet() //打印 Follow 集合
{
    cout << "FollowSet:" << endl;
    for (unsigned i = 0; i < NTs.size(); ++i) {
        set<char>::iterator it;
        if (NTs[i].FollowSet.size() == 0)
            NTs[i].FollowSet.insert('#');
        it = NTs[i].FollowSet.begin();
        cout << NTs[i].m_name << "\t: ";
        while (it != NTs[i].FollowSet.end()) {
            cout << *it;
            ++it;
        }
        cout << endl;
    }
    cout << endl;
}

//Follow集合计算法则
//0.将 # 加入到开始符Follow集合中
//1.对于每一个产生式中的非终结符 A ，若后面是终结符，则将该终结符加入集合
//2.若后面是非终结符A，且不可推空，   则将First(A) 加入集合
//3.若后面是非终结符A，且可推空，     则将First(A) 和 Follow(left) 一并加入集合

void getFollowSet()
{
    NTs[NTIdMap[Start]].FollowSet.insert('#');
    while (true) {
        bool hasUpdate = false;
        for (unsigned i = 0; i < Fs.size(); i++) {
            unsigned right_size = Fs[i].right.size();
            for (unsigned j = 0; j < right_size - 1; j++) {
                char judgeChar = Fs[i].right[j];
                char backChar = Fs[i].right[j + 1];
                if (isNT(judgeChar)) {
                    if (isT(backChar)) {
                        if (NTs[NTIdMap[judgeChar]].FollowSet.insert(backChar).second)
                            hasUpdate = true;
                    } else {
                        if (unionSet(NTs[NTIdMap[judgeChar]].FollowSet, NTs[NTIdMap[backChar]].FirstSet))
                            hasUpdate = true;
                        if (NTs[NTIdMap[backChar]].is_empty == TO_EMPTY)
                            if (unionSet(NTs[NTIdMap[judgeChar]].FollowSet, NTs[NTIdMap[Fs[i].left]].FollowSet))
                                hasUpdate = true;
                    }
                }
            }
            if (isNT(Fs[i].right[right_size - 1])) {
                if (unionSet(NTs[NTIdMap[Fs[i].right[right_size - 1]]].FollowSet, NTs[NTIdMap[Fs[i].left]].FollowSet))
                    hasUpdate = true;
            }
        }
        if (!hasUpdate)
            break;
    }
    printFollowSet();
}

//LL1文法判别法则
//相同左部的产生式 SelectSet 无交集

bool isLL1() //判别是否是LL1文法
{
    bool charHash[256] = { 0 };
    char preChar = 0;
    for (unsigned i = 0; i < Fs.size(); ++i) {
        if (Fs[i].left != preChar) //左部不同 清空 hash数组
            memset(charHash, 0, sizeof(charHash));
        preChar = Fs[i].left;
        set<char>::iterator it = Fs[i].SelectSet.begin();
        while (it != Fs[i].SelectSet.end()) {
            if (charHash[(int)*it]) //左部相同的产生式select集合两两不能有交集
                return false;
            else
                charHash[(int)*it] = true;
            it++;
        }
    }
    return true;
}

//Select集合计算法则
//1.若一个产生式可推空，则集合为该产生式的First集合
//2.否则，集合为First集合与Follow集合并集再减去空元素

void printSelectSet()
{
    cout << "SelectSet:" << endl;
    for (unsigned i = 0; i < Fs.size(); ++i) {
        set<char>::iterator it = Fs[i].SelectSet.begin();

        cout << Fs[i].left << "->" << Fs[i].right << " \t: ";
        while (it != Fs[i].SelectSet.end()) {
            cout << *it;
            ++it;
        }
        cout << endl;
    }
    cout << endl;
}

void getSelectSet() //获取Select集合
{
    for (unsigned i = 0; i < Fs.size(); ++i) {
        unionSet(Fs[i].SelectSet, Fs[i].FirstSet);
        if (Fs[i].is_empty == TO_EMPTY) {
            unionSet(Fs[i].SelectSet, NTs[NTIdMap[Fs[i].left]].FollowSet);
        }
    }
    printSelectSet();
}

void getAnalysisTable() //获取产生式select分析表
{
    Ts.push_back(T('#'));
    TIdMap.insert(make_pair('#', TIdMap.size()));
    AnalysisTable = new formula[NTs.size() * (Ts.size() + 1)];

    for (unsigned i = 0; i < Fs.size(); ++i) {
        set<char>::iterator it = Fs[i].SelectSet.begin();
        while (it != Fs[i].SelectSet.end()) {
            AnalysisTable[Ts.size() * NTIdMap[Fs[i].left] + TIdMap[*it]] = Fs[i];
            ++it;
        }
    }
}

formula analysisTableAt(char NTchar, char Tchar) //根据字符获取产生式Select
{
    return AnalysisTable[Ts.size() * NTIdMap[NTchar] + TIdMap[Tchar]];
}

formula analysisTableAt(int i, int j) //根据下标获取产生式Select
{
    return AnalysisTable[Ts.size() * i + j];
}

void printAnalysisTable() //打印产生式Select分析表
{
    int tsz = Ts.size(), ntsz = NTs.size();
    for (int i = 0; i < (tsz + 1) * 9; ++i)
        cout << "=";
    cout << endl
         << "|     |";
    for (int i = 0; i < tsz; ++i)
        cout << "   " << Ts[i].m_name << "   |";
    cout << endl;
    for (int i = 0; i < ntsz; ++i) {
        cout << "| " << NTs[i].m_name << "   |";
        for (int j = 0; j < tsz; ++j)
            printf("%5s  |", analysisTableAt(i, j).right.c_str());
        cout << endl;
    }
    for (int i = 0; i < (tsz + 1) * 9; ++i)
        cout << "=";
    cout << endl;
}

void mainControl() //分析操作
{
    char tar[1010];
    string str;
    vector<char> ST;
    int it = 0, n = 1;
    cout << "请输入分析串：(长度小于1000)" << endl;
    cin >> str;
    cout << str << endl;
    str += '#';
    strcpy(tar, str.c_str());
    for (unsigned i = 0; i < (Ts.size() + 1) * 9; ++i)
        cout << "=";
    cout << endl;
    ST.push_back('#');
    ST.push_back(Start);

    while (true) {
        if (*ST.rbegin() == '#' && tar[it] == '#') { //向量为空且匹配完成
            cout << n++ << "\t";
            for (unsigned i = 0; i < ST.size(); i++)
                cout << ST[i];
            cout << "\t\t" << tar[it] << "\t\t"
                 << "分析成功" << endl;
            break;
        }
        if (isT(*ST.rbegin())) {           //向量末尾为终结符
            if (*ST.rbegin() == tar[it]) { //且与待匹配字符相同
                cout << n++ << "\t";
                for (unsigned i = 0; i < ST.size(); i++)
                    cout << ST[i];
                cout << "\t\t" << tar + it << "\t\t" << tar[it] << "匹配" << endl;
                it++;
                ST.pop_back();
                continue;
            } else {
                cout << "不匹配" << endl;
                break;
            }
        }

        formula f = analysisTableAt(*ST.rbegin(), tar[it]);
        if (f.right == "&") { //产生式右部为空
            cout << n++ << "\t";
            for (unsigned i = 0; i < ST.size(); i++)
                cout << ST[i];
            cout << "\t\t" << tar[it] << "\t\t" << f.left << "->" << f.right << endl;
            ST.pop_back(); //直接推出
        } else {
            cout << n++ << "\t";
            for (unsigned i = 0; i < ST.size(); i++)
                cout << ST[i];
            printf("\t\t%s", tar + it);
            cout << "\t\t" << f.left << "->" << f.right << endl;
            ST.pop_back();
            for (int i = f.right.size() - 1; i >= 0; i--)
                ST.push_back(f.right[i]); //将产生式右部加入向量
        }
    }
}

int main()
{
    FP = freopen("compile_input", "r", stdin);
    readNT();              //读入非终结符
    readT();               //读入终结符
    cin >> Start;          //读入开始符
    cin >> FormulaNumber;  //读入产生式数量
    readFormula();         //读入产生式
    printFormula();        //打印产生式
    judgeNTIsEmpty();      //推导非终结符能否会产生空
    judgeFormulaIsEmpty(); //推导产生式能否产生空
    getFirstSet();         //获取First集合
    getFormulaFirstSet();  //获取产生式First集合
    getFollowSet();
    getSelectSet(); //获取select集合
    if (isLL1()) {  //如果是LL1文法
        cout << "=======此文法符合LL(1)文法========" << endl;
        getAnalysisTable();   // 获取产生式select分析表AT[u,v]，如果u想推导出select的v，需要那些转换
        printAnalysisTable(); //打印产生式select分析表
        mainControl();        //分析操作
    } else {
        cout << "=======此文法不符合LL(1)文法========" << endl;
        getAnalysisTable();
        printAnalysisTable();
    }
    return 0;
}
