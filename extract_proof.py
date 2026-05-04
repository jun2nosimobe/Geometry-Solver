import re
import os
import sys

def clean_node_name(text):
    """
    内部システム用のサフィックスやノイズを削除し、
    人間が読みやすい幾何学的な名前に整形する。
    """
    # 内部タグの削除
    text = re.sub(r'_\(Ghost\)', '', text)
    text = re.sub(r'_\(Auto\)', '', text)
    text = re.sub(r'_\(Target\)', '', text)
    
    # 冗長なクラス名の省略 (オプション)
    text = text.replace('LineThroughPoints_', 'Line_')
    text = text.replace('DirectionOf_', 'Dir_')
    text = text.replace('AnglePair_', '∠')
    text = text.replace('Circumcircle', 'Circle')
    return text

def extract_proof_from_log(log_filename):
    proof_steps = []
    seen_conclusions = set()

    # ファイルの存在チェック
    if not os.path.exists(log_filename):
        print(f"❌ エラー: ファイル '{log_filename}' が見つかりません。")
        return

    with open(log_filename, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    # ログファイルの「【証明のトレース】」セクション以降を対象にする
    trace_started = False
    for line in lines:
        if "【証明のトレース" in line:
            trace_started = True
            continue
        
        if trace_started and "🟢" in line:
            # "1. 🟢 AnglePair... ≡ AnglePair... <= 円周角の定理" の形式をパース
            match = re.search(r'🟢\s*(.+?)\s*<=\s*(.+)', line)
            if not match:
                continue

            conclusion = match.group(1).strip()
            reason = match.group(2).strip()

            # 内部タグをクリーニング
            clean_conclusion = clean_node_name(conclusion)

            # --- 無駄の排除 1: 同語反復 (A ≡ A) をスキップ ---
            if " ≡ " in clean_conclusion:
                left, right = clean_conclusion.split(" ≡ ")
                if left.strip() == right.strip():
                    continue  # 全く同じもののマージは無視
                    
            # --- 無駄の排除 2: 空のノードを含むものをスキップ ---
            if "__" in clean_conclusion or clean_conclusion.startswith("≡"):
                continue

            # --- 無駄の排除 3: 重複した結論をスキップ ---
            fact_str = f"{clean_conclusion} (by {reason})"
            
            if fact_str not in seen_conclusions:
                seen_conclusions.add(fact_str)
                proof_steps.append((clean_conclusion, reason))

    if not proof_steps:
        print(f"⚠️ '{log_filename}' から有効な証明ステップが見つかりませんでした。")
        return

    # ==========================================
    # 🌟 ファイル出力処理
    # ==========================================
    # 元のファイル名 (パスが含まれていてもファイル名だけ抽出)
    base_name = os.path.basename(log_filename)
    output_filename = f"extracted_{base_name}"

    # 書き込みモード ('w') でファイルを作成・保存
    with open(output_filename, 'w', encoding='utf-8') as out_f:
        out_f.write("="*50 + "\n")
        out_f.write("✨ 復元された証明トレース ✨\n")
        out_f.write("="*50 + "\n\n")
        
        for i, (conclusion, reason) in enumerate(proof_steps, 1):
            out_f.write(f"Step {i:2d}: {conclusion}\n")
            out_f.write(f"         └─ 理由: {reason}\n\n")

    print(f"✅ 抽出完了: '{output_filename}' に結果を保存しました。")


if __name__ == "__main__":
    # 🌟 ターミナルから `python extract_proof.py proof_40.log` のように実行可能にする
    if len(sys.argv) > 1:
        target_file = sys.argv[1]
    else:
        # 引数がない場合のデフォルトファイル
        target_file = "proof.log"
        
    extract_proof_from_log(target_file)