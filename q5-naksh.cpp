#include <fstream>
#include <cctype>
// C++17 heuristic. Model data: https://norvig.com/ngrams/
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <limits>
#include <numeric>
#include <queue>
#include <random>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
namespace document_lego {
extern const char MODEL[];
static constexpr double TIME_LIMIT = 1.65;
static constexpr int MAX_W = 60, MAX_H = 14;
using Clock = chrono::steady_clock;
auto startTime = Clock::now();
double elapsed() { return chrono::duration<double>(Clock::now()-startTime).count(); }
int letter(unsigned char c) { if(c>='A'&&c<='Z')c+=32; return c>='a'&&c<='z' ? c-'a'+1 : 0; }
uint64_t hashText(const string &s) { uint64_t h=1; for(unsigned char c:s) h=h*29+letter(c)+1; return h; }
struct Language {
unordered_map<uint64_t,double> count;
double uni[27]{}, bi[27][27]{}, tri[27][27][27]{};
double total=0, context[27][27]{};
void addWord(const string &word,double w) {
if(word.empty() || word.size()>30)return;
string s=" "+word+" ";
for(int i=0;i<(int)s.size();++i) {
uint64_t hash=1;
for(int j=i;j<(int)s.size() && j-i<26;++j) {
hash=hash*29+letter(s[j])+1; count[hash]+=w;
}
int c=letter(s[i]); uni[c]+=w; total+=w;
if(i)bi[letter(s[i-1])][c]+=w;
if(i>1) { int a=letter(s[i-2]),b=letter(s[i-1]);tri[a][b][c]+=w;context[a][b]+=w; }
}
count[hashText(" ")]-=w;uni[0]-=w;total-=w;
}
void init() {
string alphabet="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/", bytes;
int acc=0,bits=0;
for(const char *ptr=MODEL;*ptr;++ptr) {char c=*ptr;
auto d=alphabet.find(c); if(d==string::npos)continue;
acc=((acc<<6)|int(d))&0xffffff; bits+=6;
if(bits>=8) { bits-=8;bytes+=char((acc>>bits)&255); }
}
unsigned size=0;for(int j=0;j<4;++j)size|=unsigned((unsigned char)bytes[j])<<(8*j);
size_t bit=32;auto readBit=[&](){int v=bit/8<bytes.size()?((unsigned char)bytes[bit/8]>>(7-bit%8))&1:0;++bit;return v;};
vector<unsigned> zeros(65536,1),ones(65536,1);
uint32_t lo=0,hi=0xffffffff,value=0;
for(int j=0;j<32;++j)value=value*2+readBit();
string plain;plain.reserve(size);int previousByte=0;
while(plain.size()<size){
int prefix=1,c=0;
for(int j=0;j<8;++j){int k=previousByte*256+prefix;uint32_t mid=lo+(uint64_t(hi)-lo+1)*zeros[k]/(zeros[k]+ones[k])-1;
int v=value>mid;
if(v){lo=mid+1;++ones[k];}else{hi=mid;++zeros[k];}
if(zeros[k]+ones[k]>32000){zeros[k]=(zeros[k]+1)/2;ones[k]=(ones[k]+1)/2;}
for(;;){
if(hi<0x80000000u){}
else if(lo>=0x80000000u){lo-=0x80000000u;hi-=0x80000000u;value-=0x80000000u;}
else if(lo>=0x40000000u&&hi<0xc0000000u){lo-=0x40000000u;hi-=0x40000000u;value-=0x40000000u;}
else break;
lo*=2;hi=hi*2+1;value=value*2+readBit();
}
prefix=prefix*2+v;c=c*2+v;
}
plain+=char(c);previousByte=c;
}
count.reserve(350000);
string previous; size_t i=0;
while(i<plain.size()) {
int prefix=(unsigned char)plain[i++]-33, q=(unsigned char)plain[i++];
size_t end=plain.find(' ',i);
string word=previous.substr(0,prefix)+plain.substr(i,end-i);
double weight=pow(2.,(q&31)*.75);addWord(word,weight);
if(word.size()>=3){
auto ends=[&](const string&t){return word.size()>=t.size()&&word.compare(word.size()-t.size(),t.size(),t)==0;};
bool cy=ends("y")&&string("aeiou").find(word[word.size()-2])==string::npos;
if(q&32)addWord(cy?word.substr(0,word.size()-1)+"ies":word+(ends("s")||ends("x")||ends("z")||ends("ch")||ends("sh")?"es":"s"),weight*.35);
if(q&64)addWord(ends("e")?word+"d":cy?word.substr(0,word.size()-1)+"ied":word+"ed",weight*.3);
if(q&128)addWord(ends("ie")?word.substr(0,word.size()-2)+"ying":ends("e")&&!ends("ee")?word.substr(0,word.size()-1)+"ing":word+"ing",weight*.3);
}
previous=word;i=end+1;
}
}
double charLogP(const string &s)const {
if(s.empty())return 0;
double lp=0;
for(int i=0;i<(int)s.size();++i) {
int c=letter(s[i]); double p=(uni[c]+1)/(total+27);
if(i) {int b=letter(s[i-1]);p=(bi[b][c]+10*p)/(uni[b]+10);}
if(i>1) {int a=letter(s[i-2]),b=letter(s[i-1]);p=(tri[a][b][c]+20*p)/(context[a][b]+20);}
lp+=log(max(p,1e-12));
}
return lp;
}
double logp(const string &s)const {
auto it=count.find(hashText(s));
double observed=it==count.end()?0:it->second/total;
return log(max(1e-100,observed+.025*exp(charLogP(s))));
}
} lm;
struct Boundary { string token; double lp,cp; unsigned char c; bool padding; };
Boundary boundary(const string&s,bool tail) {
Boundary b; b.c=tail?s.back():s.front(); b.padding=b.c==' ';
if(!letter(b.c)) b.token=" ";
else if(tail) {
int i=(int)s.size()-1; while(i>=0&&letter(s[i]))--i;
b.token=s.substr(i+1); for(char&c:b.token)c=char('a'+letter(c)-1);
if(i>=0)b.token=" "+b.token;
}else {
int i=0;while(i<(int)s.size()&&letter(s[i]))++i;
b.token=s.substr(0,i);for(char&c:b.token)c=char('a'+letter(c)-1);
if(i<(int)s.size())b.token+=' ';
}
if(b.token.size()>24)b.token=tail?b.token.substr(b.token.size()-24):b.token.substr(0,24);
b.lp=lm.logp(b.token);b.cp=lm.charLogP(b.token);return b;
}
double join(const Boundary&a,const Boundary&b) {
bool al=letter(a.c),bl=letter(b.c);
bool ad=a.c>='0'&&a.c<='9',bd=b.c>='0'&&b.c<='9';
if(ad&&bd)return 2.;
if(!al&&!bl) {
if(a.c==' '&&b.c==' ')return -.15;
if(a.c==' ' && (b.c=='.'||b.c==','||b.c==';'||b.c==':'))return -5.;
if(a.c!=' '&&b.c!=' ')return -2.;
return .1;
}
double s=lm.logp(a.token+b.token)-a.lp-b.lp;
double cs=lm.charLogP(a.token+b.token)-a.cp-b.cp;
s=max(s,.8*cs-1.7);
if(al&&bl&&a.c>='a'&&a.c<='z'&&b.c>='A'&&b.c<='Z')s-=7;
if(a.c=='-'&&bl)s-=1;
return max(-12.,min(12.,s));
}
struct Piece { int h,w,ink;vector<string> rows;vector<Boundary> left,right; };
struct Edge {int a,b,dy,rows;float score,priority;};
struct Cluster {
vector<int> members;
int h=0,w=0;
vector<string> text;
vector<vector<int>> owner;
};
struct State {
vector<Cluster> clusters;
vector<int> root,y,x;
double quality=0;
};
vector<Piece> pieces;
vector<Edge> edges;
State initialState() {
int n=pieces.size(); State s; s.clusters.resize(n);s.root.resize(n);s.y.assign(n,0);s.x.assign(n,0);
iota(s.root.begin(),s.root.end(),0);
for(int i=0;i<n;++i) {
auto &c=s.clusters[i];auto&p=pieces[i];c.members={i};c.h=p.h;c.w=p.w;c.text=p.rows;c.owner.assign(p.h,vector<int>(p.w,i));
}
return s;
}
struct MergeInfo {bool ok=false;double score=0;int horizontal=0,vertical=0,dy=0,dx=0,holes=0;};
MergeInfo inspect(const State&s,int ra,int rb,int dy,int dx) {
MergeInfo out;out.dy=dy;out.dx=dx;
const auto &a=s.clusters[ra],&b=s.clusters[rb];
int top=min(0,dy),left=min(0,dx),bottom=max(a.h,dy+b.h),right=max(a.w,dx+b.w);
if(bottom-top>MAX_H||right-left>MAX_W)return out;
out.holes=(bottom-top)*(right-left)-a.h*a.w-b.h*b.w;
for(int r=max(0,dy);r<min(a.h,dy+b.h);++r)
for(int c=max(0,dx);c<min(a.w,dx+b.w);++c)
if(a.owner[r][c]>=0&&b.owner[r-dy][c-dx]>=0)return out;
auto owner=[&](int r,int c,int which)->int {
if(which==0)return r>=0&&r<a.h&&c>=0&&c<a.w?a.owner[r][c]:-1;
r-=dy;c-=dx;return r>=0&&r<b.h&&c>=0&&c<b.w?b.owner[r][c]:-1;
};
auto chr=[&](int r,int c,int which)->char { return which==0?a.text[r][c]:b.text[r-dy][c-dx]; };
for(int r=top;r<bottom;++r){
bool previousSpace=false,padding=false;
for(int c=left;c<right;++c){
int side=owner(r,c,0)>=0?0:owner(r,c,1)>=0?1:-1;
if(side<0){previousSpace=false;continue;}
bool space=chr(r,c,side)==' ';
if(space&&previousSpace)padding=true;
if(!space&&padding)return out;
previousSpace=space;
}
}
for(int r=top;r<bottom;++r)for(int c=left;c+1<right;++c) {
int wa=owner(r,c,0)>=0?0:owner(r,c,1)>=0?1:-1;
if(wa<0||owner(r,c+1,wa)>=0||owner(r,c+1,1-wa)<0)continue;
string l,t;
for(int q=c;q>=left&&c-q<24&&owner(r,q,wa)>=0;--q)l+=chr(r,q,wa);
reverse(l.begin(),l.end());
for(int q=c+1;q<right&&q-c<=24&&owner(r,q,1-wa)>=0;++q)t+=chr(r,q,1-wa);
double sc=join(boundary(l,true),boundary(t,false));
out.score+=sc; ++out.horizontal;
}
for(int r=top;r+1<bottom;++r)for(int c=left;c<right;++c) {
if((owner(r,c,0)>=0&&owner(r+1,c,1)>=0)||(owner(r,c,1)>=0&&owner(r+1,c,0)>=0))++out.vertical;
}
out.ok=true;return out;
}
void mergeClusters(State&s,int ra,int rb,const MergeInfo&m) {
auto &a=s.clusters[ra],&b=s.clusters[rb];
int minr=min(0,m.dy),minc=min(0,m.dx);
Cluster c;c.h=max(a.h,m.dy+b.h)-minr;c.w=max(a.w,m.dx+b.w)-minc;
c.text.assign(c.h,string(c.w,' '));c.owner.assign(c.h,vector<int>(c.w,-1));
c.members=a.members;c.members.insert(c.members.end(),b.members.begin(),b.members.end());
for(int id:c.members) {
s.y[id]+=(s.root[id]==rb?m.dy:0)-minr;s.x[id]+=(s.root[id]==rb?m.dx:0)-minc;s.root[id]=ra;
for(int r=0;r<pieces[id].h;++r)for(int col=0;col<pieces[id].w;++col) {
c.text[s.y[id]+r][s.x[id]+col]=pieces[id].rows[r][col];c.owner[s.y[id]+r][s.x[id]+col]=id;
}
}
s.quality+=m.score+.03*m.vertical;
a=std::move(c);b=Cluster();
}
void buildEdges() {
int n=pieces.size();vector<vector<Edge>> candidates(n);
struct Top {double first=-1e6,second=-1e6;int key=-1;
void add(double s,int k){if(k==key){first=max(first,s);return;}if(s>first){second=first;first=s;key=k;}else second=max(second,s);}
double other(int k)const{return k==key?second:first;}
};
vector<Top> leftBest(n*225),rightBest(n*225);
bool stopped=false;
for(int a=0;a<n&&!stopped;++a) {
vector<Edge> local;
for(int b=0;b<n;++b)if(a!=b&&pieces[a].w+pieces[b].w<=MAX_W) {
if((b&15)==0&&elapsed()>TIME_LIMIT*.48){stopped=true;break;}
const auto &p=pieces[a],&q=pieces[b];float scores[14][14];
for(int r=0;r<p.h;++r)for(int t=0;t<q.h;++t)scores[r][t]=join(p.right[r],q.left[t]);
for(int dy=1-q.h;dy<p.h;++dy) {
int h=max(p.h,dy+q.h)-min(0,dy);if(h>MAX_H)continue;
float score=0;int cnt=0;
for(int r=max(0,dy);r<min(p.h,dy+q.h);++r){score+=scores[r][r-dy];++cnt;}
for(int lo=max(0,dy);lo<min(p.h,dy+q.h);++lo){double v=0;for(int hi=lo+1;hi<=min(p.h,dy+q.h);++hi){v+=scores[hi-1][hi-1-dy];leftBest[a*225+lo*15+hi].add(v,b*32+dy+14);rightBest[b*225+(lo-dy)*15+hi-dy].add(v,a*32+dy+14);}}
int holes=h*(p.w+q.w)-p.w*p.h-q.w*q.h;
if(score>.5) local.push_back({a,b,dy,cnt,score,score-.45f*holes});
}
}
sort(local.begin(),local.end(),[](const Edge&a,const Edge&b){return a.score>b.score;});
if(local.size()>100)local.resize(100);
candidates[a]=std::move(local);
}
for(int a=0;a<n;++a)for(auto e:candidates[a]) {
int lo=max(0,e.dy),hi=min(pieces[a].h,e.dy+pieces[e.b].h);
double l=e.score-leftBest[a*225+lo*15+hi].other(e.b*32+e.dy+14);
double r=e.score-rightBest[e.b*225+(lo-e.dy)*15+hi-e.dy].other(a*32+e.dy+14);
l=min(12.,l);r=min(12.,r);
e.priority=min(l,r)+.25*max(l,r);edges.push_back(e);
}
}
double objective(const State&s) {
double value=s.quality;
for(int i=0;i<(int)pieces.size();++i)if(s.root[i]==i) {
auto &c=s.clusters[i];int area=0;
for(int p:c.members)area+=pieces[p].h*pieces[p].w;
value-=.45*(c.h*c.w-area);
}
return value;
}
vector<vector<int>> incident;
struct Proposal {
double priority;int a,b,dy,dx,va,vb;MergeInfo m;
bool operator<(const Proposal&o)const{return priority<o.priority;}
};
State solve(mt19937&rng,int attempt) {
State s=initialState();vector<int> version(pieces.size());
priority_queue<Proposal> heap;
uniform_real_distribution<double> u(0,1);
double noise=attempt==0?0:(attempt%3==1?.45:.9);
double gap=attempt%4==0?.30:attempt%4==1?.15:attempt%4==2?.5:.22;
auto push=[&](int a,int b,int dy,int dx,double confidence) {
auto m=inspect(s,a,b,dy,dx);if(!m.ok||!m.horizontal)return;
double score=(m.score-1.2*m.horizontal)*sqrt(double(m.horizontal))-.30*max(0,m.holes)+.04*m.vertical;
score+=(.3-gap)*max(0,m.holes);
score+=.9*confidence;
if(score<=0)return;
score+=noise*(-log(max(1e-8,u(rng)))-.5772);
heap.push({score,a,b,dy,dx,version[a],version[b],m});
};
int prepared=0;
for(auto&e:edges){if((++prepared&255)==0&&elapsed()>TIME_LIMIT*.94)break;push(e.a,e.b,e.dy,pieces[e.a].w,e.priority);}
while(!heap.empty()&&elapsed()<TIME_LIMIT) {
auto p=heap.top();heap.pop();
if(version[p.a]!=p.va||version[p.b]!=p.vb||s.root[p.a]!=p.a||s.root[p.b]!=p.b)continue;
mergeClusters(s,p.a,p.b,p.m);++version[p.a];++version[p.b];
unordered_set<uint64_t> tried;
for(int id:s.clusters[p.a].members)for(int k:incident[id]) {
if((k&255)==0&&elapsed()>TIME_LIMIT)return s;
auto&e=edges[k];int a=s.root[e.a],b=s.root[e.b];if(a==b)continue;
int dy=s.y[e.a]+e.dy-s.y[e.b],dx=s.x[e.a]+pieces[e.a].w-s.x[e.b];
if(a>b){swap(a,b);dy=-dy;dx=-dx;}
uint64_t key=uint64_t(a);key=key*pieces.size()+b;key=key*65+dy+32;key=key*257+dx+128;
if(tried.insert(key).second)push(a,b,dy,dx,e.priority);
}
}
return s;
}
vector<vector<int>> run(const vector<string>& input) {
startTime = Clock::now();
pieces.clear(); edges.clear(); incident.clear(); lm = Language{};
int n = static_cast<int>(input.size());
vector<vector<int>> result;
result.reserve(n);
for (int i=0;i<n;++i) result.push_back({i,i,0,0});
if (n==0) return result;
pieces.reserve(n);
for (int i=0;i<n;++i) {
string line=input[i];
if (!line.empty() && line.back()=='\r') line.pop_back();
Piece p; p.ink=0; string row;
for (size_t j=0;j<=line.size();++j) {
if (j==line.size() || line[j]=='|') { p.rows.push_back(row); row.clear(); }
else { char c=line[j]=='_'?' ':line[j]; row+=c; p.ink+=c!=' '; }
}
p.h=p.rows.size(); p.w=p.rows.empty()?0:p.rows[0].size();
if (!p.w || p.h>MAX_H || p.w>MAX_W) return result;
for (const auto& r:p.rows) if (static_cast<int>(r.size())!=p.w) return result;
pieces.push_back(std::move(p));
}
lm.init();
unordered_map<string,int> visible;
for(const auto&p:pieces)for(const auto&r:p.rows)for(int i=0;i<(int)r.size();) {
if(!letter(r[i])){++i;continue;}int begin=i;string w;
while(i<(int)r.size()&&letter(r[i]))w+=char('a'+letter(r[i++])-1);
if(begin>0&&i<(int)r.size())++visible[w];
}
for(auto&it:visible)lm.addWord(it.first,20.*it.second);
for(auto&p:pieces)for(auto&r:p.rows){p.left.push_back(boundary(r,false));p.right.push_back(boundary(r,true));}
buildEdges();
incident.resize(n);for(int k=0;k<(int)edges.size();++k){incident[edges[k].a].push_back(k);incident[edges[k].b].push_back(k);}
mt19937 rng(712367);State best=initialState();double bestScore=-1e100;int attempts=0;
do {
State current=solve(rng,attempts++);double value=objective(current);
if(value>bestScore){bestScore=value;best=std::move(current);}
}while(attempts<32&&elapsed()<TIME_LIMIT*.88);
for (int i=0;i<n;++i) result[i]={i,best.root[i],best.y[i],best.x[i]};
return result;
}
const char MODEL[] =
"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"
;
}
vector<vector<int>> assemble(vector<string> pieces) { return document_lego::run(pieces); }
int main() {
ofstream fout(getenv("OUTPUT_PATH"));
string line;
getline(cin,line);
int n=stoi(line);
vector<string> pieces(n);
for (int i=0;i<n;++i) getline(cin,pieces[i]);
auto result=assemble(pieces);
for (const auto& row:result) {
for (size_t j=0;j<row.size();++j) fout<<(j?" ":"")<<row[j];
fout<<"\n";
}
}
