#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <math.h>
#include <algorithm>
#include <algorithm>
#include <random>
#include <cstdint>
#include <chrono>
using namespace std;

// defining block size and integer size
static int blockSize = 4;
static int integerSize = 32;

// Count the number of 1s in B[1...x]
int rank1(unsigned int bitvector, int x)
{
    int count = 0;
    for (int i = 0; i < x; i++)
    {
        count += (bitvector & 1); // Add 1 if the last bit is 1
        bitvector >>= 1;         // Shift the bitvector to the right
    }
    return count;
}

// Count the number of 0s in B[1...x]
int rank0(unsigned int bitvector, int x)
{
    int count = 0;
    for (int i = 0; i < x; i++)
    {
        if ((bitvector & 1) == 0)   // Add 1 if the last bit is 0
        {
            count++;
        }
        bitvector >>= 1;           // Shift the bitvector to the right
    }
    return count;
}

// Radix sort implementaion


// Compare two pairs (a1, a2) and (b1, b2) lexicographically
inline bool leq(int a1, int a2, int b1, int b2)
{
    // Return true if (a1, a2) <= (b1, b2)
    return (a1 < b1) || (a1 == b1 && a2 <= b2);
}

// Compare two triples (a1, a2, a3) and (b1, b2, b3) lexicographically
inline bool leq(int a1, int a2, int a3, int b1, int b2, int b3)
{
    // Return true if (a1, a2, a3) <= (b1, b2, b3)
    return (a1 < b1) || (a1 == b1 && leq(a2, a3, b2, b3));
}


// Stably sort array `a[0..n-1]` into array `b[0..n-1]` using keys in `r` with range 0..K
static void radixPass(int* a, int* b, int* r, int n, int K)
{
    // Step 1: Count occurrences
    int* count = new int[K + 1]; // Counter array for keys
    for (int i = 0; i <= K; i++)
    {
        count[i] = 0; // Initialize counters to zero
    }

    for (int i = 0; i < n; i++)
    {
        count[r[a[i]]]++; // Count occurrences of each key
    }

    // Step 2: Compute exclusive prefix sums for stable sorting
    for (int i = 0, sum = 0; i <= K; i++)
    {
        int temp = count[i];
        count[i] = sum; // Store the starting position of each key
        sum += temp;    // Update cumulative sum
    }

    // Step 3: Sort elements based on keys
    for (int i = 0; i < n; i++)
    {
        b[count[r[a[i]]]++] = a[i]; // Place elements into sorted order
    }

    // Step 4: Clean up memory
    delete[] count;
}

// Function to construct the suffix array using the DC3 (Difference Cover) algorithm
void suffixArray(int* s, int* SA, int n, int K)
{
    // Step 1: Divide the input into three groups
    int n0 = (n + 2) / 3;   // Positions mod 3 == 0
    int n1 = (n + 1) / 3;   // Positions mod 3 == 1
    int n2 = n / 3;         // Positions mod 3 == 2
    int n02 = n0 + n2;      // Total positions mod 3 != 0

    // Arrays for suffixes in mod 1 and mod 2 positions
    int* s12 = new int[n02 + 3]; // Extra space for padding
    int* SA12 = new int[n02 + 3];
    s12[n02] = s12[n02 + 1] = s12[n02 + 2] = 0;
    SA12[n02] = SA12[n02 + 1] = SA12[n02 + 2] = 0;

    // Arrays for suffixes in mod 0 positions
    int* s0 = new int[n0];
    int* SA0 = new int[n0];

    // Step 2: Generate s12 (positions mod 1 and mod 2)
    for (int i = 0, j = 0; i < n + (n0 - n1); i++)
    {
        if (i % 3 != 0)
        {
            s12[j++] = i;
        }
    }

    // Step 3: Sort s12 using radix sort
    radixPass(s12, SA12, s + 2, n02, K); // Sort by third character
    radixPass(SA12, s12, s + 1, n02, K); // Sort by second character
    radixPass(s12, SA12, s, n02, K);     // Sort by first character

    // Step 4: Assign names to sorted triplets
    int name = 0, c0 = -1, c1 = -1, c2 = -1;
    for (int i = 0; i < n02; i++)
    {
        if (s[SA12[i]] != c0 || s[SA12[i] + 1] != c1 || s[SA12[i] + 2] != c2)
        {
            name++; // New triplet
            c0 = s[SA12[i]];
            c1 = s[SA12[i] + 1];
            c2 = s[SA12[i] + 2];
        }
        if (SA12[i] % 3 == 1)
        {
            s12[SA12[i] / 3] = name; // Group 1
        }
        else
        {
            s12[SA12[i] / 3 + n0] = name; // Group 2
        }
    }

    // Step 5: Recurse if names are not unique
    if (name < n02)
    {
        suffixArray(s12, SA12, n02, name); // Recursive call
        for (int i = 0; i < n02; i++)
        {
            s12[SA12[i]] = i + 1; // Renumber suffixes
        }
    }
    else
    {
        for (int i = 0; i < n02; i++)
        {
            SA12[s12[i] - 1] = i;
        }
    }

    // Step 6: Sort mod 0 suffixes
    for (int i = 0, j = 0; i < n02; i++)
    {
        if (SA12[i] < n0)
        {
            s0[j++] = 3 * SA12[i];
        }
    }
    radixPass(s0, SA0, s, n0, K);

    // Step 7: Merge sorted mod 0 and mod 1/2 suffixes
    for (int p = 0, t = n0 - n1, k = 0; k < n; k++)
    {
#define GetI() (SA12[t] < n0 ? SA12[t] * 3 + 1 : (SA12[t] - n0) * 3 + 2)
        int i = GetI(); // Current suffix from mod 1/2
        int j = SA0[p]; // Current suffix from mod 0

        // Merge condition
        if (SA12[t] < n0
                ? leq(s[i], s12[SA12[t] + n0], s[j], s12[j / 3])
                : leq(s[i], s[i + 1], s12[SA12[t] - n0 + 1], s[j], s[j + 1], s12[j / 3 + n0]))
        {
            SA[k] = i;
            t++;
            if (t == n02)   // Append remaining mod 0 suffixes
            {
                for (k++; p < n0; p++, k++) SA[k] = SA0[p];
            }
        }
        else
        {
            SA[k] = j;
            p++;
            if (p == n0)   // Append remaining mod 1/2 suffixes
            {
                for (k++; t < n02; t++, k++) SA[k] = GetI();
            }
        }
    }

    // Cleanup
    delete[] s12;
    delete[] SA12;
    delete[] s0;
    delete[] SA0;
}


// Builds the Burrows-Wheeler Transform (BWT) from the Suffix Array
int BurrowsWheelerTransform(int* s, int* BWT, int* SA, int n)
{
    int maxValue = std::numeric_limits<int>::min(); // Initialize to the smallest possible value

    // Construct the BWT
    for (int i = 0; i < n; i++)
    {
        int j = SA[i] - 1; // Get the previous character's position
        if (j < 0)
        {
            j += n; // Wrap around if the position is negative
        }
        BWT[i] = s[j]; // Set the BWT value at position i
        maxValue = std::max(BWT[i], maxValue); // Track the maximum value in the BWT
    }

    return maxValue; // Return the maximum value in the BWT
}


//Reading text file
std::string readTXTFile(const char* filename)
{
    std::FILE* fp = std::fopen(filename, "rb");
    if (fp)
    {
        std::string filecontent;
        std::fseek(fp, 0, SEEK_END);
        filecontent.resize(std::ftell(fp));
        std::rewind(fp);
        std::fread(&filecontent[0], 1, filecontent.size(), fp);
        std::fclose(fp);
        return(filecontent);
    }
    throw(errno);
}


class waveletTree
{
public:
    int minval, maxval;                        // Range of values represented by this node
    waveletTree* left = nullptr;               // Pointer to left child node
    waveletTree* right = nullptr;              // Pointer to right child node
    std::vector<unsigned int> packedArray;     // Packed bit vector for this node
    std::vector<int> indexArray;               // Cumulative rank array for blocks

    // Constructor to build the wavelet tree
    waveletTree(int* beg, int* endp, int low, int high)
    {
        unsigned int packedBits = 0;           // Renamed from currentInteger
        int bitIdx = 0;                        // Renamed from bitPosition
        int onesCount = 0;                     // Renamed from oneCount

        minval = low;
        maxval = high;

        // Base case: If the range is empty, return
        if (beg >= endp)
        {
            return;
        }

        // Reserve space for packedArray based on the range size
        packedArray.reserve(ceil((endp - beg + 1) / blockSize));

        // Case 1: All elements in this range are equal
        if (maxval == minval)
        {
            for (auto it = beg; it < endp; it++)
            {
                bitIdx = ((it - beg) % integerSize);
                packedBits += pow(2, bitIdx); // Set the bit at the current position
                onesCount++;
                // Push the packed integer when the block is full
                if (bitIdx == (integerSize - 1))
                {
                    packedArray.push_back(packedBits);
                    packedBits = 0;
                }
                // Update cumulative rank when a block is full
                if (bitIdx == (blockSize - 1))
                {
                    indexArray.push_back(onesCount + (indexArray.empty() ? 0 : indexArray.back()));
                    onesCount = 0;
                }
            }
            // Push remaining bits for incomplete blocks
            if (bitIdx != (integerSize - 1))
            {
                packedArray.push_back(packedBits);
            }
            if (bitIdx != (blockSize - 1))
            {
                indexArray.push_back(onesCount + (indexArray.empty() ? 0 : indexArray.back()));
            }
            return;
        }

        // Case 2: Split the range into two halves
        int midVal = (minval + maxval) / 2;    // Renamed from mid

        // Lambda function to check if a value is less than or equal to the midpoint
        auto isLessOrEqualToMid = [midVal](int x)
        {
            return x <= midVal;
        };

        // Partition the range and populate packedArray and indexArray
        for (auto it = beg; it < endp; it++)
        {
            int isGreater = !isLessOrEqualToMid(*it);  // 1 if greater than mid, 0 otherwise
            bitIdx = ((it - beg) % integerSize);
            packedBits += isGreater * pow(2, bitIdx); // Set the bit
            onesCount += isGreater;
            // Push the packed integer when the block is full
            if (bitIdx == (integerSize - 1))
            {
                packedArray.push_back(packedBits);
                packedBits = 0;
            }
            // Update cumulative rank when a block is full
            if ((bitIdx + 1) % blockSize == 0)
            {
                indexArray.push_back(onesCount + (indexArray.empty() ? 0 : indexArray.back()));
                onesCount = 0;
            }
        }
        // Push remaining bits for incomplete blocks
        if (bitIdx != (integerSize - 1))
        {
            packedArray.push_back(packedBits);
        }
        if (bitIdx != (blockSize - 1))
        {
            indexArray.push_back(onesCount + (indexArray.empty() ? 0 : indexArray.back()));
        }

        // Partition the range into two parts: left and right
        auto pivot = stable_partition(beg, endp, isLessOrEqualToMid);

        // Recursively build left and right subtrees
        left = new waveletTree(beg, pivot, minval, midVal);
        right = new waveletTree(pivot, endp, midVal + 1, maxval);
    }



// Printing packed array
    void print()
    {
        for (int i = 0; i < packedArray.size(); i++)
        {
            cout << packedArray.at(i) << ", ";
        }
        cout << "\n";
    }

    int rank(int charVal, int queryIndex)
    {
        // Lambda function to check if a value is less than or equal to the midpoint
        auto isLessOrEqualToMid = [this](int x)
        {
            return x <= (minval + maxval) / 2;
        };

        // Base case: All values in this range are the same
        if (minval == maxval)
        {
            return queryIndex;
        }
        else
        {
            int arrayIndex = queryIndex / integerSize;           // Index of the integer in packedArray
            int blockIndex = queryIndex / blockSize;             // Index of the block in indexArray
            int bitOffset = queryIndex % integerSize;            // Bit offset within the current integer
            unsigned int bitVector = packedArray[arrayIndex] >> ((bitOffset / blockSize) * blockSize); // Extract relevant bits
            int localBitIndex = bitOffset % blockSize;           // Bit position within the block

            // Check if the character is in the left subtree
            if (isLessOrEqualToMid(charVal))
            {
                int result = rank0(bitVector, localBitIndex);     // Compute rank0 (number of 0s)
                if (blockIndex > 0)
                {
                    result += blockSize * (blockIndex) - indexArray[blockIndex - 1]; // Adjust for previous blocks
                }
                return (*left).rank(charVal, result);            // Recursive call to left subtree
            }
            else
            {
                // Character is in the right subtree
                int result = rank1(bitVector, localBitIndex);     // Compute rank1 (number of 1s)
                if (blockIndex > 0)
                {
                    result += indexArray[blockIndex - 1];        // Adjust for previous blocks
                }
                return (*right).rank(charVal, result);           // Recursive call to right subtree
            }
        }
    }
};
// Implementing backward pattern matching using FM-index
int patternMatching(int patternLength, int pattern[], int* charTable, int start, int end, waveletTree wtTree)
{
    int matchCount = 1;  // Counter for matches

    // Iterate over the pattern from the last character to the first
    for (int i = patternLength - 1; i >= 0; i--)
    {
        int charPosition = pattern[i];  // Current character position in the pattern

        // Update the start and end range using the wavelet tree and character table
        start = charTable[charPosition] + wtTree.rank(charPosition, start - 1) + 1;
        end = charTable[charPosition] + wtTree.rank(charPosition, end);
    }

    // Return the number of matches found in the range
    return end - start + 1;
}



void computeCharacterRank(int* charTable, int* suffixArray, int* input, int length)
{
    int frequencyCount = 1;  // Counter for character frequency

    // Iterate through the suffix array to compute character ranks
    for (int i = 1; i < length; i++)
    {
        // If consecutive characters are the same, increment the frequency count
        if (input[suffixArray[i]] == input[suffixArray[i - 1]])
        {
            frequencyCount++;
        }
        else
        {
            // Update the character rank table for the current character
            charTable[input[suffixArray[i]]] = charTable[input[suffixArray[i - 1]]] + frequencyCount;
            frequencyCount = 1;  // Reset the frequency count for the next character
        }
    }
}


void printTotalSpace(int textLength, int alphabetSize)
{
    size_t inputTextSpace = sizeof(char) * textLength;
    size_t textArraySpace = sizeof(int) * (textLength + 3);
    size_t suffixArraySpace = sizeof(int) * (textLength + 1);
    size_t bwtSpace = sizeof(int) * textLength;
    size_t waveletTreeSpace = textLength * log2(alphabetSize) / 8; // Approximation

    size_t totalSpace = inputTextSpace + textArraySpace + suffixArraySpace + bwtSpace + waveletTreeSpace;

    cout << "Space Breakdown (in MB):\n";
    cout << "Input Text: " << inputTextSpace / (1024.0 * 1024.0) << " MB\n";
    cout << "Text Array: " << textArraySpace / (1024.0 * 1024.0) << " MB\n";
    cout << "Suffix Array: " << suffixArraySpace / (1024.0 * 1024.0) << " MB\n";
    cout << "BWT: " << bwtSpace / (1024.0 * 1024.0) << " MB\n";
    cout << "Wavelet Tree: " << waveletTreeSpace / (1024.0 * 1024.0) << " MB\n";
    cout << "Total Space: " << totalSpace / (1024.0 * 1024.0) << " MB\n";
}


int main()
{
    cout << "Reading text file \n";
    string input = readTXTFile("D:\\LSU\\Fall_24\\CSC7300\\algo_project\\dna_50mb.txt");
    int textLength = input.size();

    int n = input.size();
    int* textArray = new int[n + 3];

    for (int i = 0; i < n; i++)
        textArray[i] = (int)input[i];

    cout << "Creating suffix array\n";
    namespace sc = std::chrono;
    auto timenow = sc::system_clock::now();
    auto timeSinceEpoch = timenow.time_since_epoch();
    auto timemillisec = sc::duration_cast<sc::milliseconds>(timeSinceEpoch);
    long startTime = timemillisec.count();
    int* SA = new int[n + 1];
    int K = 128;
    int* C = new int[K];
    std::fill(C, C + K, 0);
    suffixArray(textArray, SA, n, K);
    timenow = sc::system_clock::now();
    timeSinceEpoch = timenow.time_since_epoch();
    timemillisec = sc::duration_cast<sc::milliseconds>(timeSinceEpoch);
    long endTime = timemillisec.count();
    cout << "Suffix Array Creation Time: " << endTime-startTime << " milliseconds.\n";

    int startPoint = 1, endPoint = n;;
    cout << "Building Burrows-Wheeler Transform (BWT) from suffix array : \n";
    int* bwtArray = new int[n];

    int maximum = BurrowsWheelerTransform(textArray, bwtArray, SA, n);

    cout << "Constructing Wavelet Tree\n";
    timenow = sc::system_clock::now();
    timeSinceEpoch = timenow.time_since_epoch();
    timemillisec = sc::duration_cast<sc::milliseconds>(timeSinceEpoch);
    startTime = timemillisec.count();
    waveletTree wt = waveletTree(bwtArray, bwtArray + n, 64, maximum);
    timenow = sc::system_clock::now();
    timeSinceEpoch = timenow.time_since_epoch();
    timemillisec = sc::duration_cast<sc::milliseconds>(timeSinceEpoch);
    endTime = timemillisec.count();
    cout << "Wavelet Tree Creation Time: " << endTime-startTime << " milliseconds.\n";

    computeCharacterRank(C, SA, textArray, n);
    cout << "Backward Pattern Matching\n";
    string pattern;
    cout << "Enter Pattern: ";
    cin >> pattern;

    int P[pattern.length()];
    for (int i = 0; i < pattern.length(); i++)
    {
        P[i] = (int)pattern[i];
    }

    timenow = sc::system_clock::now();
    timeSinceEpoch = timenow.time_since_epoch();
    timemillisec = sc::duration_cast<sc::milliseconds>(timeSinceEpoch);
    startTime = timemillisec.count();

    int flag = 0;
    flag = patternMatching(pattern.length(), P, C, startPoint, endPoint, wt);

    if(flag == 0)
    {
        cout << "No Pattern Matches.\n";
    }
    else
    {
        cout << flag << " Patterns found.\n";
    }

    timenow = sc::system_clock::now();
    timeSinceEpoch = timenow.time_since_epoch();
    timemillisec = sc::duration_cast<sc::milliseconds>(timeSinceEpoch);
    endTime = timemillisec.count();

    cout << "Pattern Matching Time: " << endTime-startTime << " milliseconds.\n";

    delete textArray;
    delete SA;
    delete bwtArray;

    // Calculate and print total space usage
    int alphabetSize = 128; // ASCII size
    printTotalSpace(textLength, alphabetSize);

    return 0;

}
