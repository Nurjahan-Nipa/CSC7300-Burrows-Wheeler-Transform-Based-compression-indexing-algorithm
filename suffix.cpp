#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>


using namespace std;

// Function to construct the suffix array
vector<int> buildSuffixArray(const string &text) {
    int n = text.size();
    vector<int> suffixArray(n), ranks(n), temp(n);
    vector<pair<char, int>> initialRanks(n);

    // Step 1: Initial sorting by the first character
    for (int i = 0; i < n; i++)
        initialRanks[i] = {text[i], i};
    sort(initialRanks.begin(), initialRanks.end());

    for (int i = 0; i < n; i++) {
        suffixArray[i] = initialRanks[i].second;
        ranks[suffixArray[i]] = (i > 0 && initialRanks[i].first == initialRanks[i - 1].first) ? ranks[suffixArray[i - 1]] : i;
    }

    // Step 2: Sorting by first 2^k characters using radix sorting
    for (int k = 1; k < n; k *= 2) {
        vector<int> count(n, 0), nextSuffixArray(n);
        for (int i = 0; i < n; i++) count[ranks[i]]++;

        for (int i = 1; i < n; i++) count[i] += count[i - 1];
        for (int i = n - 1; i >= 0; i--) {
            int prevIndex = (suffixArray[i] - k + n) % n;
            nextSuffixArray[--count[ranks[prevIndex]]] = prevIndex;
        }
        suffixArray = nextSuffixArray;

        // Update ranks
        temp[suffixArray[0]] = 0;
        for (int i = 1; i < n; i++) {
            pair<int, int> prev = {ranks[suffixArray[i - 1]], ranks[(suffixArray[i - 1] + k) % n]};
            pair<int, int> curr = {ranks[suffixArray[i]], ranks[(suffixArray[i] + k) % n]};
            temp[suffixArray[i]] = (prev == curr) ? temp[suffixArray[i - 1]] : i;
        }
        ranks = temp;
    }
    return suffixArray;
}



// Function to count occurrences of the pattern using binary search on the suffix array
int countPatternOccurrences(const string &text, const vector<int> &suffixArray, const string &pattern) {
    int n = text.size(), m = pattern.size();
    int left = 0, right = n - 1;

    // Binary search to find the first occurrence of the pattern
    while (left <= right) {
        int mid = (left + right) / 2;
        string suffix = text.substr(suffixArray[mid], min(n - suffixArray[mid], m));
        if (suffix >= pattern)
            right = mid - 1;
        else
            left = mid + 1;
    }
    int start = left;

    // Binary search to find the last occurrence of the pattern
    right = n - 1;
    while (left <= right) {
        int mid = (left + right) / 2;
        string suffix = text.substr(suffixArray[mid], min(n - suffixArray[mid], m));
        if (suffix > pattern)
            right = mid - 1;
        else
            left = mid + 1;
    }
    int end = right;

    // Return the count of matches
    return max(0, end - start + 1);
}

void printMemoryUsage(size_t textLength, size_t suffixArraySize) {
    size_t inputTextSpace = sizeof(char) * textLength;                      // Input text
    size_t suffixArraySpace = sizeof(int) * suffixArraySize;                // Suffix array
    size_t rankSpace = sizeof(int) * textLength;                            // Ranks
    size_t tempSpace = sizeof(int) * textLength;                            // Temporary array
    size_t initialRanksSpace = sizeof(pair<char, int>) * textLength;        // Initial ranks

    size_t totalSpace = inputTextSpace + suffixArraySpace + rankSpace + tempSpace + initialRanksSpace;

    //cout << "Memory Usage Breakdown (in MB):\n";
    //cout << "Input Text: " << inputTextSpace / (1024.0 * 1024.0) << " MB\n";
    //cout << "Suffix Array: " << suffixArraySpace / (1024.0 * 1024.0) << " MB\n";
    //cout << "Ranks: " << rankSpace / (1024.0 * 1024.0) << " MB\n";
    //cout << "Temporary Array: " << tempSpace / (1024.0 * 1024.0) << " MB\n";
    //cout << "Initial Ranks: " << initialRanksSpace / (1024.0 * 1024.0) << " MB\n";
    cout << "Total Memory Usage: " << totalSpace / (1024.0 * 1024.0) << " MB\n";
}


int main() {
    // Step 1: Load the large dataset
    cout << "Reading the dataset...\n";
    ifstream file("D:\\LSU\\Fall_24\\CSC7300\\algo_project\\dna_50mb.txt"); // Change to your dataset path
    string text;
    if (file.is_open()) {
        text.assign((istreambuf_iterator<char>(file)), istreambuf_iterator<char>());
        file.close();
    } else {
        cerr << "Error: Unable to open the file.\n";
        return 1;
    }
    text += "$"; // Add a sentinel character to the text

    // Step 2: Build the suffix array
    cout << "Building suffix array...\n";
    auto startTime = chrono::high_resolution_clock::now();
    vector<int> suffixArray = buildSuffixArray(text);
    auto endTime = chrono::high_resolution_clock::now();
    cout << "Suffix array built in "
         << chrono::duration_cast<chrono::milliseconds>(endTime - startTime).count()
         << " ms.\n";



    // Step 3: Pattern matching
    string pattern;
    cout << "Enter the pattern to search: ";
    cin >> pattern;

    startTime = chrono::high_resolution_clock::now();
    int count = countPatternOccurrences(text, suffixArray, pattern);
    endTime = chrono::high_resolution_clock::now();

    // Output the results
    if (count == 0) {
        cout << "Pattern not found.\n";
    } else {
        cout << "Pattern found " << count << " times.\n";
    }
    cout << "Pattern search completed in "
         << chrono::duration_cast<chrono::milliseconds>(endTime - startTime).count()
         << " ms.\n";

    size_t textLength = text.size();

    // Print memory usage
    printMemoryUsage(textLength, suffixArray.size());

    return 0;
}
